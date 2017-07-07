#include <stdio.h>
#include <stdlib.h>
#define uchar	unsigned char
#define ulong	unsigned long
#define ushort	unsigned short
#define uint    unsigned int
#ifndef SSIZE
#define SSIZE 18
#endif
#ifndef MSIZE
#define MSIZE 18
#endif

/******************  BCAN Error Procs ******************************/

void wrapup(int arg) {
  int *n = 0;
  *n = 999; /* help! */
}

void uerror(char *str) {
  printf("%s\n",str);
  wrapup(0);
}

void Uerror(char *str) {
  uerror(str);
}

/*****************End BCAN Error Procs *****************************/


/**************** Memory management ********************************/
#define VECTORSZ	1024           /* sv   size in bytes */


#ifdef MEMCNT
double memcnt = (double) 0;
double overhead = (double) 0;
double memlim = (double) (1<<30);
#endif
/* for emalloc: */
static char *have;
static long left = 0L;
static double fragment = (double) 0;
static unsigned long grow;


char *
Malloc(unsigned n)
{	char *tmp;
#ifdef MEMCNT
	if (memcnt+ (double) n > memlim) goto err;
#endif
	tmp = (char *) sbrk(n);
	if ((int) tmp == -1)
	{
err:
		printf("bcan: out of memory\n");
#ifdef MEMCNT
		printf("	%g bytes used\n", memcnt);
		printf("	%g bytes more needed\n", (double) n);
		printf("	%g bytes limit (2^MEMCNT)\n",
			memlim);
#endif
		wrapup(0);
	}
#ifdef MEMCNT
	memcnt += n;
#endif
	return tmp;
}

#define CHUNK	(100*VECTORSZ)

char *
emalloc(unsigned n) /* never released or reallocated */
{	char *tmp;
	if (n == 0)
	        return (char *) NULL;
	if (n&(sizeof(void *)-1)) /* for proper alignment */
	        n += sizeof(void *)-(n&(sizeof(void *)-1));
	if (left < n)
	{       grow = (n < CHUNK) ? CHUNK : n;
	        have = Malloc(grow);
	        fragment += (double) left;
	        left = grow;
	}
	tmp = have;
	have += (long) n;
	left -= (long) n;
	memset(tmp, 0, n);
	return tmp;
}

/**************** End of memory management *************************/

/******************* Graph Encoding ********************************/

#define TWIDTH		256
#define HASH(y,n)	(n)*(((int)y))
#define INRANGE(e,h)	((h>=e->From && h<=e->To)||(e->s==1 && e->S==h))

extern char	*emalloc(unsigned);	/* 1 imported routine  */
extern void	dfa_init(ushort);	/* 4 exported routines */
extern int	dfa_member(ushort);
extern int	dfa_store(uchar *);
extern void	dfa_stats(void);

typedef struct Edge {
	uchar From, To;		/* max range 0..255 */
	uchar s, S;		/* if s=1, S is singleton */
	struct Vertex	*Dst;
	struct Edge	*Nxt;
} Edge;

typedef struct Vertex {
	ulong	key, num;	/* key for splay tree, nr incoming edges */
	uchar	from[2], to[2];	/* in-node predefined edge info    */
	struct	Vertex	*dst[2];/* most nodes have 2 or more edges */
	struct	Edge	*Succ;	/* in case there are more edges */
	struct	Vertex	*lnk, *left, *right; /* splay tree plumbing */
} Vertex;

static ulong    nr_states = 0;
static Edge	*free_edges;
static Vertex	*free_vertices;
static Vertex	**layers;	/* one splay tree of nodes per layer */
static Vertex	**path;		/* run of word in the DFA */
static Vertex	*R, *F, *NF;	/* Root, Final, Not-Final */
static uchar	*word, *lastword;/* string, and last string inserted */
static int	dfa_depth, iv=0, nv=0, pfrst=0, Tally;

static void	insert_it(Vertex *, int);	/* splay-tree code */
static void	delete_it(Vertex *, int);
static Vertex	*find_it(Vertex *, Vertex *, uchar, int);

static void
recyc_edges(Edge *e)
{
	if (!e) return;
	recyc_edges(e->Nxt);
	e->Nxt = free_edges;
	free_edges = e;
}

static Edge *
new_edge(Vertex *dst)
{	Edge *e;

	if (free_edges)
	{	e = free_edges;
		free_edges = e->Nxt;
		e->From = e->To = e->s = e->S = 0;
		e->Nxt = (Edge *) 0;
	} else
		e = (Edge *) emalloc(sizeof(Edge));
	e->Dst = dst;

	return e;
}

static void
recyc_vertex(Vertex *v)
{
	recyc_edges(v->Succ);
	v->Succ = (Edge *) free_vertices;
	free_vertices = v;
	nr_states--;
}

static Vertex *
new_vertex(void)
{	Vertex *v;

	if (free_vertices)
	{	v = free_vertices;
		free_vertices = (Vertex *) v->Succ;
		v->Succ = (Edge *) 0;
		v->num  = 0;
	} else
		v = (Vertex *) emalloc(sizeof(Vertex));

	nr_states++;
	return v; 
}

static Vertex *
allDelta(Vertex *v, int n)
{	Vertex *dst = new_vertex();

	v->from[0] = 0;
	v->to[0] = 255;
	v->dst[0] = dst;
	dst->num = 256;
	insert_it(v, n);
	return dst;
}

static void
insert_edge(Vertex *v, Edge *e)
{	/* put new edge first */
	if (!v->dst[0])
	{	v->dst[0] = e->Dst;
		v->from[0] = e->From;
		v->to[0] = e->To;
		recyc_edges(e);
		return;
	}
	if (!v->dst[1])
	{	v->from[1] = v->from[0]; v->from[0] = e->From;
		v->to[1]   = v->to[0];   v->to[0]   = e->To;
		v->dst[1]  = v->dst[0];  v->dst[0]  = e->Dst;
		recyc_edges(e);
		return;
	} /* shift */
	{	int f      = v->from[1];
		int t      = v->to[1];
		Vertex *d  = v->dst[1];
		v->from[1] = v->from[0]; v->from[0] = e->From;
		v->to[1]   = v->to[0];   v->to[0]   = e->To;
		v->dst[1]  = v->dst[0];  v->dst[0]  = e->Dst;
		e->From = f;
		e->To   = t;
		e->Dst  = d;
	}
	e->Nxt = v->Succ;
	v->Succ = e;
}

static void
copyRecursive(Vertex *v, Edge *e)
{	Edge *f;
	if (e->Nxt) copyRecursive(v, e->Nxt);
	f = new_edge(e->Dst);
	f->From = e->From;
	f->To   = e->To;
	f->s    = e->s;
	f->S    = e->S;
	f->Nxt  = v->Succ;
	v->Succ = f;
}

static void
copyEdges(Vertex *to, Vertex *from)
{	int i;
	for (i = 0; i < 2; i++)
	{	to->from[i] = from->from[i];
		to->to[i]   = from->to[i];
		to->dst[i]  = from->dst[i];
	}
	if (from->Succ) copyRecursive(to, from->Succ);
}

static Edge *
cacheDelta(Vertex *v, int h, int first)
{	static Edge *ov, tmp;  int i;

	if (!first && INRANGE(ov,h))
		return ov; /* intercepts about 10% */
	for (i = 0; i < 2; i++)
		if (v->dst[i] && h >= v->from[i] && h <= v->to[i])
		{	tmp.From = v->from[i];
			tmp.To   = v->to[i];
			tmp.Dst  = v->dst[i];
			tmp.s    =  tmp.S = 0;
			ov = &tmp;
			return ov;
		}
	for (ov = v->Succ; ov; ov = ov->Nxt)
		if (INRANGE(ov,h)) return ov;

	Uerror("cannot get here, cacheDelta");
	return (Edge *) 0;
}

static Vertex *
Delta(Vertex *v, int h)	/* v->delta[h] */
{	register Edge *e;

	if (v->dst[0] && h >= v->from[0] && h <= v->to[0])
		return v->dst[0];	/* oldest edge */
	if (v->dst[1] && h >= v->from[1] && h <= v->to[1])
		return v->dst[1];
	for (e = v->Succ; e; e = e->Nxt)
		if (INRANGE(e,h))
			return e->Dst;
	Uerror("cannot happen Delta");
	return (Vertex *) 0;
}

static void
numDelta(Vertex *v, int d)
{	register Edge *e;
	register ulong cnt;
	int i;

	for (i = 0; i < 2; i++)
	if (v->dst[i])
	{	cnt = v->dst[i]->num + d*(1 + v->to[i] - v->from[i]);
		if (d == 1 && cnt < v->dst[i]->num) goto bad;
		v->dst[i]->num = cnt;
	}
	for (e = v->Succ; e; e = e->Nxt)
	{	cnt = e->Dst->num + d*(1 + e->To - e->From + e->s);
		if (d == 1 && cnt < e->Dst->num)
bad:			Uerror("too many incoming edges");
		e->Dst->num = cnt;
	}
}

static void
setDelta(Vertex *v, int h, Vertex *newdst)	/* v->delta[h] = newdst; */
{	Edge *e, *f = (Edge *) 0, *g;
	int i;

	/* remove the old entry, if there */
	for (i = 0; i < 2; i++)
		if (v->dst[i] && h >= v->from[i] && h <= v->to[i])
		{	if (h == v->from[i])
			{	if (h == v->to[i])
				{	v->dst[i] = (Vertex *) 0;
					v->from[i] = v->to[i] = 0;
				} else
					v->from[i]++;
			} else if (h == v->to[i])
			{	v->to[i]--;
			} else
			{	g = new_edge(v->dst[i]);/* same dst */
				g->From    = v->from[i];
				g->To      = h-1;	/* left half */
				v->from[i] = h+1;	/* right half */
				insert_edge(v, g);
			}
			goto part2;
		}
	for (e = v->Succ; e; f = e, e = e->Nxt)
	{	if (e->s == 1 && e->S == h)
		{	e->s = e->S = 0;
			goto rem_tst;
		}
		if (h >= e->From && h <= e->To)
		{	if (h == e->From)
			{	if (h == e->To)
				{	if (e->s)
					{	e->From = e->To = e->S;
						e->s = 0;
						break;
					} else
						goto rem_do;
				} else
					e->From++;
			} else if (h == e->To)
			{	e->To--;
			} else				/* split */
			{	g = new_edge(e->Dst);	/* same dst */
				g->From = e->From;
				g->To   = h-1;		/* g=left half */
				e->From = h+1;		/* e=right half */
				g->Nxt  = e->Nxt;	/* insert g */
				e->Nxt  = g;		/* behind e */
				break;			/* done */
			}

rem_tst:		if (e->From > e->To)
			{	if (e->s == 0) {
rem_do:				if (f)
						f->Nxt = e->Nxt;
					else
						v->Succ = e->Nxt;
					e->Nxt = (Edge *) 0;
					recyc_edges(e);
				} else
				{	e->From = e->To = e->S;
					e->s = 0;
			}	}
			break;
	}	}
part2:
	/* check if newdst is already there */
	for (i = 0; i < 2; i++)
		if (v->dst[i] == newdst)
		{	if (h+1 == (int) v->from[i])
			{	v->from[i] = h;
				return;
			}
			if (h == (int) v->to[i]+1)
			{	v->to[i] = h;
				return;
		}	}
	for (e = v->Succ; e; e = e->Nxt)
	{	if (e->Dst == newdst)
		{	if (h+1 == (int) e->From)
			{	e->From = h;
				if (e->s == 1 && e->S+1 == e->From)
				{	e->From = e->S;
					e->s = e->S = 0;
				}
				return;
			}
			if (h == (int) e->To+1)
			{	e->To = h;
				if (e->s == 1 && e->S == e->To+1)
				{	e->To = e->S;
					e->s = e->S = 0;
				}
				return;
			}
			if (e->s == 0)
			{	e->s = 1;
				e->S = h;
				return;
	}	}	}
	/* add as a new edge */
	e = new_edge(newdst);
	e->From = e->To = h;
	insert_edge(v, e);
}

static ulong
cheap_key(Vertex *v)
{	ulong vk2 = 0;

	if (v->dst[0])
	{	vk2 = (ulong) v->dst[0];
		if ((ulong) v->dst[1] > vk2)
			vk2 = (ulong) v->dst[1];
	} else if (v->dst[1])
		vk2 = (ulong) v->dst[1]; 
	if (v->Succ)
	{	Edge *e;
		for (e = v->Succ; e; e = e->Nxt)
			if ((ulong) e->Dst > vk2)
				vk2 = (ulong) e->Dst;
	}
	Tally = (vk2>>2)&(TWIDTH-1);
	return v->key;
}

static ulong
mk_key(Vertex *v)	/* not sensitive to order */
{	register ulong m = 0, vk2 = 0;
	register Edge *e;

	if (v->dst[0])
	{	m += HASH(v->dst[0], v->to[0] - v->from[0] + 1);
		vk2 = (ulong) v->dst[0]; 
	}
	if (v->dst[1])
	{	m += HASH(v->dst[1], v->to[1] - v->from[1] + 1);
		if ((ulong) v->dst[1] > vk2) vk2 = (ulong) v->dst[1]; 
	}
	for (e = v->Succ; e; e = e->Nxt)
	{	m += HASH(e->Dst, e->To - e->From + 1 + e->s);
		if ((ulong) e->Dst > vk2) vk2 = (ulong) e->Dst; 
	}
	Tally = (vk2>>2)&(TWIDTH-1);
	return m;
}

static ulong
mk_special(int sigma, Vertex *n, Vertex *v)
{	register ulong m = 0, vk2 = 0;
	register Edge *f; Vertex *last = (Vertex *) 0;
	int i;

	for (i = 0; i < 2; i++)
		if (v->dst[i])
		{	if (sigma >= v->from[i] && sigma <= v->to[i])
			{	m += HASH(v->dst[i], v->to[i]-v->from[i]);
				if ((ulong) v->dst[i] > vk2
				&&   v->to[i] > v->from[i])
					vk2 = (ulong) v->dst[i]; 
			} else
			{	m += HASH(v->dst[i], v->to[i]-v->from[i]+1);
				if ((ulong) v->dst[i] > vk2)
					vk2 = (ulong) v->dst[i]; 
		}	}
	for (f = v->Succ; f; f = f->Nxt)
	{	if (sigma >= f->From && sigma <= f->To)
		{	m += HASH(f->Dst, f->To - f->From + f->s);
			if ((ulong) f->Dst > vk2
			&&   f->To - f->From + f->s > 0)
				vk2 = (ulong) f->Dst; 
		} else if (f->s == 1 && sigma == f->S)
		{	m += HASH(f->Dst, f->To - f->From + 1);
			if ((ulong) f->Dst > vk2) vk2 = (ulong) f->Dst; 
		} else
		{	m += HASH(f->Dst, f->To - f->From + 1 + f->s);
			if ((ulong) f->Dst > vk2) vk2 = (ulong) f->Dst; 
	}	}

	if ((ulong) n > vk2) vk2 = (ulong) n; 
	Tally = (vk2>>2)&(TWIDTH-1);
	m += HASH(n, 1);
	return m;
}

void 
dfa_init(ushort nr_layers)
{	int i; Vertex *r, *t;

	dfa_depth = nr_layers;	/* one byte per layer */
	path   = (Vertex **) emalloc((dfa_depth+1)*sizeof(Vertex *));
	layers = (Vertex **) emalloc(TWIDTH*(dfa_depth+1)*sizeof(Vertex *));
	lastword = (uchar *) emalloc((dfa_depth+1)*sizeof(uchar));
	lastword[dfa_depth] = lastword[0] = 255;
	path[0] = R = new_vertex(); F = new_vertex();

	for (i = 1, r = R; i < dfa_depth; i++, r = t)
		t = allDelta(r, i-1);
	NF = allDelta(r, i-1);
}

#if 0
static void complement_dfa(void) { Vertex *tmp = F; F = NF; NF = tmp; }
#endif

double
tree_stats(Vertex *t)
{	Edge *e; double cnt=0.0;
	if (!t) return 0;
	if (!t->key) return 0;
	t->key = 0; /* precaution */
	if (t->dst[0]) cnt++;
	if (t->dst[1]) cnt++;
	for (e = t->Succ; e; e = e->Nxt)
		cnt++;
	cnt += tree_stats(t->lnk);
	cnt += tree_stats(t->left);
	cnt += tree_stats(t->right);
	return cnt;
}

void
dfa_stats(void)
{	int i, j; double cnt = 0.0;
	for (j = 0; j < TWIDTH; j++)
	for (i = 0; i < dfa_depth+1; i++)
		cnt += tree_stats(layers[i*TWIDTH+j]);
	printf("Minimized Automaton:	%6d nodes and %6g edges\n",
		nr_states, cnt);
}

int
dfa_member(ushort n)
{	Vertex **p, **q;
	uchar *w = &word[n];
	int i;

	p = &path[n]; q = (p+1);
	for (i = n; i < dfa_depth; i++)
		*q++ = Delta(*p++, *w++);
	return (*p == F);
}

int
dfa_store(uchar *sv)
{	Vertex **p, **q, *s, *y, *old, *new = F;
	uchar *w, *u = lastword;
	int i, j, k;

	w = word = sv;
	while (*w++ == *u++)	/* find first byte that differs */
		;
	pfrst = (int) (u - lastword) - 1;
	memcpy(&lastword[pfrst], &sv[pfrst], dfa_depth-pfrst);
	if (pfrst > iv) pfrst = iv;
	if (pfrst > nv) pfrst = nv;
phase1:
	p = &path[pfrst]; q = (p+1); w = &word[pfrst];
	for (i = pfrst; i < dfa_depth; i++)
		*q++ = Delta(*p++, *w++);	/* (*p)->delta[*w++]; */

	if (*p == F) return 1;	/* it's already there */
phase2:
	iv = dfa_depth;
	do {	iv--;
		old = new;
		new = find_it(path[iv], old, word[iv], iv);
	} while (new && iv > 0);

phase3:
	nv = k = 0; s = path[0];
	for (j = 1; j <= iv; ++j) 
		if (path[j]->num > 1)
		{	y = new_vertex();
			copyEdges(y, path[j]);
			insert_it(y, j);
			numDelta(y, 1);
			delete_it(s, j-1);
			setDelta(s, word[j-1], y);
			insert_it(s, j-1);
			y->num = 1;	/* initial value 1 */
			s = y;
			path[j]->num--;	/* only 1 moved from j to y */
			k = 1;
		} else
		{	s = path[j];
			if (!k) nv = j;
		}
	y = Delta(s, word[iv]);
	y->num--;
	delete_it(s, iv); 
	setDelta(s, word[iv], old);
	insert_it(s, iv); 
	old->num++;

	for (j = iv+1; j < dfa_depth; j++)
		if (path[j]->num == 0)
		{	numDelta(path[j], -1);
			delete_it(path[j], j);
			recyc_vertex(path[j]);
		} else
			break;
	return 0;
}

static Vertex *
splay(ulong i, Vertex *t)
{	Vertex N, *l, *r, *y;

	if (!t) return t;
	N.left = N.right = (Vertex *) 0;
	l = r = &N;
	for (;;)
	{	if (i < t->key)
		{	if (!t->left) break;
			if (i < t->left->key)
			{	y = t->left;
				t->left = y->right;
				y->right = t;
				t = y;
				if (!t->left) break;
			}
			r->left = t;
			r = t;
			t = t->left;
		} else if (i > t->key)
		{	if (!t->right) break;
			if (i > t->right->key)
			{	y = t->right;
				t->right = y->left;
				y->left = t;
				t = y;
				if (!t->right) break;
			}
			l->right = t;
			l = t;
			t = t->right;
		} else
			break;
	}
	l->right = t->left;
	r->left = t->right;
	t->left = N.right;
	t->right = N.left;
	return t;
}

static void
insert_it(Vertex *v, int L)
{	Vertex *new, *t;
	ulong i; int nr;

	i = mk_key(v);
	nr = ((L*TWIDTH)+Tally);
	t = layers[nr];

	v->key = i; 
	if (!t)
	{	layers[nr] = v;
		return;
	}
	t = splay(i, t);
	if (i < t->key)
	{	new = v;
		new->left = t->left;
		new->right = t;
		t->left = (Vertex *) 0;
	} else if (i > t->key)
	{	new = v;
		new->right = t->right;
		new->left = t;
		t->right = (Vertex *) 0;
	} else	 /* it's already there */
	{	v->lnk = t->lnk; /* put in linked list off v */
		t->lnk = v;
		new = t;
	}
	layers[nr] = new;
}

static int
checkit(Vertex *h, Vertex *v, Vertex *n, uchar sigma)
{	Edge *g, *f;
	int i, k, j = 1;

	for (k = 0; k < 2; k++)
		if (h->dst[k])
		{	if (sigma >= h->from[k] && sigma <= h->to[k])
			{	if (h->dst[k] != n) goto no_match;
			}
			for (i = h->from[k]; i <= h->to[k]; i++)
			{	if (i == sigma) continue;
				g = cacheDelta(v, i, j); j = 0;
				if (h->dst[k] != g->Dst)
					goto no_match;
				if (g->s == 0 || g->S != i)
					i = g->To;
		}	}
	for (f = h->Succ; f; f = f->Nxt)
	{	if (INRANGE(f,sigma))
		{	if (f->Dst != n) goto no_match;
		}
		for (i = f->From; i <= f->To; i++)
		{	if (i == sigma) continue;
			g = cacheDelta(v, i, j); j = 0;
			if (f->Dst != g->Dst)
				goto no_match;
			if (g->s == 1 && i == g->S)
				continue;
			i = g->To;
		}
		if (f->s && f->S != sigma)
		{	g = cacheDelta(v, f->S, 1);
			if (f->Dst != g->Dst)
				goto no_match;
		}
	}
	if (h->Succ || h->dst[0] || h->dst[1]) return 1;
no_match:
	return 0;
}

static Vertex *
find_it(Vertex *v, Vertex *n, uchar sigma, int L)
{	Vertex *z, *t;
	ulong i; int nr;

	i = mk_special(sigma,n,v);
	nr = ((L*TWIDTH)+Tally);
	t = layers[nr];

	if (!t) return (Vertex *) 0;
	layers[nr] = t = splay(i, t);
	if (i == t->key)
	for (z = t; z; z = z->lnk)
		if (checkit(z, v, n, sigma))
			return z;

	return (Vertex *) 0;
}

static void
delete_it(Vertex *v, int L)
{	Vertex *x, *t;
	ulong i; int nr;

	i = cheap_key(v);
	nr = ((L*TWIDTH)+Tally);
	t = layers[nr];
	if (!t) return;

	t = splay(i, t);
	if (i == t->key)
	{	Vertex *z, *y = (Vertex *) 0;
		for (z = t; z && z != v; y = z, z = z->lnk)
			;
		if (z != v) goto bad;
		if (y)
		{	y->lnk = z->lnk;
			z->lnk = (Vertex *) 0;
			layers[nr] = t;
			return;
		} else if (z->lnk)	/* z == t == v */
		{	y = z->lnk;
			y->left = t->left;
			y->right = t->right;
			t->left = t->right = t->lnk = (Vertex *) 0;
			layers[nr] = y;
			return;
		}
		/* delete the node itself */
		if (!t->left)
		{	x = t->right;
		} else
		{	x = splay(i, t->left);
			x->right = t->right;
		}
		t->left = t->right = t->lnk = (Vertex *) 0;
		layers[nr] = x;
		return;
	}
bad:	Uerror("cannot happen delete");
}

/***************** End of Graph Encoding ***************************/

/***************** Hash Table **************************************/
unsigned char 	HASH_NR = 0;

unsigned int HASH_CONST[] = {
	 
	0x88888EEF,	0x00400007,
	0x04c11db7,	0x100d4e63,
	0x0fc22f87,	0x3ff0c3ff,
	0x38e84cd7,	0x02b148e9,
	0x98b2e49d,	0xb616d379,
	0xa5247fd9,	0xbae92a15,
	0xb91c8bc5,	0x8e5880f3,
	0xacd7c069,	0xb4c44bb3,
	0x2ead1fb7,	0x8e428171,
	0xdbebd459,	0x828ae611,
	0x6cb25933,	0x86cdd651,
	0x9e8f5f21,	0xd5f8d8e7,
	0x9c4e956f,	0xb5cf2c71,
	0x2e805a6d,	0x33fc3a55,
	0xaf203ed1,	0xe31f5909,
	0x5276db35,	0x0c565ef7,
	0x273d1aa5,	0x8923b1dd,
	0
};

typedef struct H_el {
  struct H_el *nxt;
  unsigned state;
} H_el_t;

typedef struct Hash_table {
  H_el_t **H_tab;
  int    ssize;
  int    mask;
  double hcmp;
  char   *hstored;
} Hash_table_t;

void
hinit(Hash_table_t *tbl, int sz) {
  tbl->H_tab = (struct H_el **)emalloc((1<<sz)*sizeof(struct H_el *));
  tbl->mask = ((1<<sz)-1);
  tbl->ssize = sz;
  tbl->hcmp = 0;
  tbl->hstored = NULL;	 
}

long 
s_hash(Hash_table_t *tbl, unsigned char  *cp, int om) {
        long z = (long) HASH_CONST[HASH_NR];
	long *q;
	long h;
	long m = -1;
	h = (om+sizeof(long)-1)/sizeof(long);
	q = (long *) cp;
	do {
		if (m < 0)
		{	m += m;
			m ^= z;
		} else
			m += m;
		m ^= *q++;
	} while (--h > 0);
	return ((m^(m>>(8*sizeof(long)-(tbl->ssize))))&(tbl->mask)); 
}

/* hstore returns 1 if vin[0..nin] is already present else returns 0 */
int
hstore(Hash_table_t *tbl, char *vin, int nin) {	
  register struct H_el *tmp; int m=0;
  struct H_el *ntmp, *olst = (struct H_el *) 0;

  char	*v = vin;
  int	 n = nin;
  long j1 = 0;

  j1 = s_hash(tbl, (unsigned char  *)v, n);
  tmp = (tbl->H_tab)[j1];
  if (!tmp) {  
    tmp = (struct H_el *) emalloc(sizeof(struct H_el) + n - sizeof(unsigned));
    (tbl->H_tab)[j1] = tmp;
  } 
  else {  
    for (;; tbl->hcmp++, olst = tmp, tmp = tmp->nxt) {    
      m = memcmp(((char *)&(tmp->state)), v, n);
      if (m == 0) {
        tbl->hstored = (char *)(&(tmp->state));
        return 1;  
      } 
      else { 
        if (m < 0) {	 
          ntmp = (struct H_el *) emalloc(sizeof(struct H_el) + n - sizeof(unsigned)); 
          ntmp->nxt = tmp;
          if (!olst) {
            (tbl->H_tab)[j1] = ntmp;
          }
          else {
            olst->nxt = ntmp;
          }
          tmp = ntmp;
          break;
        } 
        else { 
          if (!tmp->nxt) {	 
            tmp->nxt = (struct H_el *) emalloc(sizeof(struct H_el) + n - sizeof(unsigned));
            tmp = tmp->nxt;
	    break;
          }
	}
      }   
    }
  }
  tbl->hstored = (char *)(&(tmp->state));
  memcpy(tbl->hstored, v, n);
  return 0;
}

/* hstore2 returns 0 and a copy of data if key is already present 
   else inserts key+data and returns 1 */
int
hstore2(Hash_table_t *tbl, 
        char *key, int key_n_chars, 
        char *data, int data_n_chars) {	
  register struct H_el *tmp; int m=0;
  struct H_el *ntmp, *olst = (struct H_el *) 0;
  int memreq = key_n_chars + data_n_chars;
  long j1 = 0;

  j1 = s_hash(tbl,(unsigned char  *)key, key_n_chars);
  tmp = (tbl->H_tab)[j1];
  if (!tmp) {  
    tmp = (struct H_el *) emalloc(sizeof(struct H_el) + memreq - sizeof(unsigned));
    (tbl->H_tab)[j1] = tmp;
  } 
  else {  
    for (;; tbl->hcmp++, olst = tmp, tmp = tmp->nxt) {    
      m = memcmp(((char *)&(tmp->state)), key, key_n_chars);
      if (m == 0) {
        memcpy(data, ((char *)&(tmp->state)) + key_n_chars, data_n_chars);
        return 0;  
      } 
      else { 
        if (m < 0) {	 
          ntmp = (struct H_el *) emalloc(sizeof(struct H_el) + memreq - sizeof(unsigned)); 
          ntmp->nxt = tmp;
          if (!olst) {
            (tbl->H_tab)[j1] = ntmp;
          }
          else {
            olst->nxt = ntmp;
          }
          tmp = ntmp;
          break;
        } 
        else { 
          if (!tmp->nxt) {	 
            tmp->nxt = (struct H_el *) emalloc(sizeof(struct H_el) + memreq - sizeof(unsigned));
            tmp = tmp->nxt;
	    break;
          }
	}
      }   
    }
  }
  memcpy(((char *)&(tmp->state)), key, key_n_chars);
  memcpy(((char *)&(tmp->state)) + key_n_chars, data, data_n_chars);
  return 1;
}

/***************** End Hash Table **********************************/

/**************** Stack *******************************************/

typedef struct stackElement {
  char *body;
  struct stackElement *free, *nxtElem;
} stackElement_t;

typedef struct {
  uint size;
  stackElement_t *top;
} stack_t;

stack_t *
new_stack(uint size) {
  stack_t *stack = (stack_t *)emalloc(sizeof(stack_t));
  stack->size = size;
  stack->top = (stackElement_t *)emalloc(sizeof(stackElement_t));
  return stack;
}

void
push(stack_t *stack, void *data) {
  if (!stack->top->free) {
    stack->top->free = (stackElement_t *)emalloc(sizeof(stackElement_t));
    stack->top->free->body = emalloc(stack->size);
    stack->top->free->nxtElem = stack->top;
  }
  stack->top = stack->top->free;
  memcpy(stack->top->body, (char *)data, stack->size); 
}

void
pop(stack_t *stack, void *target) {
  memcpy((char *)target, stack->top->body, stack->size);
  stack->top = stack->top->nxtElem;
} 

#define is_empty_stk(s) ((!((s)->top->body)))
#define is_non_empty_stk(s) ((((s)->top->body)))
/**************** End Stack ***************************************/

/**************** Queue *******************************************/

typedef struct queueElement {
  char *body;
  struct queueElement *nxt;
} queueElement_t;

typedef struct {
  uint size;
  queueElement_t *f, *r;
} queue_t;

queue_t *
new_queue(uint size) {
  queue_t *q = (queue_t *)emalloc(sizeof(queue_t));
  q->size = size;
  q->f = q->r = (queueElement_t *)emalloc(sizeof(queueElement_t));
  q->r->body = emalloc(size);
  q->r->nxt = q->f;       /* initially empty AND full */
  return q;
}

void
enqueue(queue_t *q, void *data) {
  if (q->r->nxt == q->f) {
    q->r->nxt = (queueElement_t *)emalloc(sizeof(queueElement_t));
    q->r->nxt->body = emalloc(q->size);
    q->r->nxt->nxt = q->f;
  }
  memcpy(q->r->body, (char *)data, q->size);
  q->r = q->r->nxt;
}

/* need to be sure queue is not empty before calling dequeue
   test for empty is (f == r)
*/
void
dequeue(queue_t *q, void *target) {
  memcpy((char *)target, q->f->body, q->size);
  q->f = q->f->nxt;
}

#define is_empty_q(q) (((q)->f == (q)->r))
#define is_non_empty_q(q) (((q)->f != (q)->r))
/**************** End Queue ***************************************/

#define N_CLOCKS 13
static short clock_max_bound[N_CLOCKS] = {0, 0, 63, 350, 1500, 15500, 300, 0, 5100, 0, 10250, 0, 5100};
/********************** DBMS **************************************/
/******************** Bounds ********************************************/
#include <limits.h>

#ifdef _INTBNDTP_
typedef int VALUE_TYPE;
#define MAX_VALUE_TYPE INT_MAX
#else
typedef short VALUE_TYPE;
#define MAX_VALUE_TYPE SHRT_MAX
#endif

typedef char SGN_TYPE;
typedef VALUE_TYPE BOUND_TYPE;

#define SGN_LE		1
#define SGN_LT		0
#define ZERO_LE		1
#define INFTY_LT	(MAX_VALUE_TYPE-1)

#define MAX_BND_VAL    ((INFTY_LT)>>1)
#define max_bnd_ge(bd) (bd>=MAX_BND_VAL)

#define mk_bound(val,sgn) ((val<<1) | sgn)
#define get_bound_value(bd) (((bd & (~1))) >> 1)
#define get_bound_sgn(bd) (bd & 1)

#define is_bound_lt(bd1,bd2) (bd1 < bd2)
#define is_bound_le(bd1,bd2) (bd1 <= bd2)
#define is_bound_gt(bd1,bd2) (bd1 > bd2)
#define is_bound_ge(bd1,bd2) (bd1 >= bd2)
#define is_bound_eq(bd1,bd2) (bd1 == bd2)
#define is_bound_neq(bd1,bd2) (bd1 != bd2)

#define add_bounds(bd1,bd2) (((bd1 & ~1) + (bd2 & ~1)) | (bd1 & bd2 & 1))

#define add_int(a,b) ((int) ((int)(a) + (int)(b)))
#define min_int(a,b) ((VALUE_TYPE) ((int)(a) < (int)(b))?(a):(b))

#ifdef _INTBNDTP_
#define add_bounds2(bd1,bd2) (VALUE_TYPE) \
        ( (max_bnd_ge(bd1)||max_bnd_ge(bd2)) ? INFTY_LT : add_bounds(bd1,bd2) )
#else
#define add_bounds2(bd1,bd2) (VALUE_TYPE) \
        ((min_int(add_int((bd1 & ~1),(bd2 & ~1)), INFTY_LT)) | (bd1 & bd2 & 1))
#endif

#define min_bound(bd1,bd2) ((bd1<bd2)?bd1:bd2)
#define compl_bound(bd) (((- (bd>>1)) << 1) | ((~bd)&1))

/**************************End Bounds************************************/


/**************************Matrix****************************************/
#ifndef DIM
#define DIM 3
#endif

static const int MATRIX_N_BYTES = sizeof(BOUND_TYPE) * DIM * DIM;

#ifdef VDIM
typedef BOUND_TYPE *MATRIX;
#else
typedef BOUND_TYPE MATRIX[DIM * DIM];
#endif

#ifdef O1
#define AT(marx,i,j) (((marx)[((i)==(j)) ? (i) : (marx)[0]+((i)*((marx)[0]-1)+(j)) - (((i)<(j)) ? 1 : 0)])) 
#elif defined(O2)
#define AT(marx,i,j) (((marx)[((i)==(j)) ? (i) : (i<j) ? ((2*(i)+1)*((marx)[0]) + (2 * (j))) - ((i) * (i) + (3 * (i)) + 2) : ((2*(j)+1)*((marx)[0]) + (2 * (i))+ 1) - ((j) * (j) + (3 * (j)) + 2)]))
#else
#define AT(marx,i,j) ((marx)[(((marx)[0]) * (i)) + (j)])
#endif

#define matrix_dimension(marx)	(((marx)[0]))
#define size_matrix(marx) \
  ((matrix_dimension(marx) * matrix_dimension(marx) * sizeof(BOUND_TYPE)))
#define is_trivial_matrix(marx)	((marx==NULL)||(matrix_dimension(marx)<2))
#define is_not_trivial_matrix(marx) ((marx!=NULL)&&(matrix_dimension(marx)>1))

#define if_restrict_bound_change(b1, b2, ch)    \
			{ if (b2 < b1) { b1 = b2; ch = 1; } }


BOUND_TYPE temp_matrix[DIM*DIM];

BOUND_TYPE new_matrix[DIM*DIM];

static uchar reset_clock[N_CLOCKS];

static uchar active_clock[N_CLOCKS];

int 
n_active_clocks () {
  int i, count = 0;
  for (i = 0; i < N_CLOCKS; i+=1) {
    if (active_clock[i]) {
      count += 1;
    }
  }
  return count;
}

char *
clock_name(int n) {
  static char name[10];
  sprintf(name, "H%d", n);
  return name;
}

void  fprint_matrix(FILE *file, MATRIX marx)
{
  int i, j, dim;

  if (is_trivial_matrix(marx)) {
    fprintf(file, "true\n");
    return;
  }
  // canonicalize_matrix(marx);
  dim = matrix_dimension(marx);
  for (i=0; i<dim; i++) {
    for (j=0; j<dim; j++)
      if (j != i)
        if (AT(marx,i,j) != INFTY_LT)
          fprintf(file, "%d,%s\t", get_bound_value(AT(marx,i,j)),
                                 get_bound_sgn(AT(marx,i,j))?"<=":"<");
        else
          fprintf(file, "inf\t");
      else if (i > 0)
        fprintf(file, "[%s]\t", clock_name(AT(marx,i,i)));
      else
        fprintf(file, "dim:%d\t", dim);
    fprintf(file, "\n");
  }
}

void  print_matrix(MATRIX marx)
{
  fprint_matrix(stdout, marx);
}

void  pretty_fprint_matrix(FILE *file, MATRIX marx)
{
  int i, j, dim;

  if (is_trivial_matrix(marx)) {
    fprintf(file, "true\n");
    return;
  }
  dim = matrix_dimension(marx);
  for (i=1; i<dim; i++)
    if (AT(marx,0,i) != ZERO_LE || AT(marx,i,0) != INFTY_LT) {
      if (((AT(marx,i,0))>>1) + ((AT(marx,0,i))>>1) == 0)
	fprintf(file, "%s=%d", clock_name(AT(marx,i,i)), (AT(marx,i,0))>>1);
      else {
        if (AT(marx,0,i) != ZERO_LE)
	  fprintf(file, "%d<%s", -((AT(marx,0,i))>>1), (AT(marx,0,i)&1)?"=":"");
        fprintf(file, "%s", clock_name(AT(marx,i,i)));
        if (AT(marx,i,0) != INFTY_LT)
	  fprintf(file, "<%s%d", (AT(marx,i,0)&1)?"=":"", (AT(marx,i,0))>>1);
      }
      fprintf(file, ", ");
    }
  for (i=1; i<dim; i++)
    for (j=i+1; j<dim; j++)
      if (AT(marx,i,j) != INFTY_LT || AT(marx,j,i) != INFTY_LT) {
	if (((AT(marx,i,j))>>1) + ((AT(marx,j,i))>>1) == 0)
	  fprintf(file, "%s-%s=%d", clock_name(AT(marx,i,i)),clock_name(AT(marx,j,j)), (AT(marx,i,j))>>1);
	else {
	  if (AT(marx,j,i) != INFTY_LT)
	    fprintf(file, "%d<%s", -((AT(marx,j,i))>>1), (AT(marx,j,i)&1)?"=":"");
	  fprintf(file, "%s-%s", clock_name(AT(marx,i,i)),clock_name(AT(marx,j,j)));
	  if (AT(marx,i,j) != INFTY_LT)
	    fprintf(file, "<%s%d", (AT(marx,i,j)&1)?"=":"", (AT(marx,i,j))>>1);
	}
        fprintf(file, ", ");
      }
  fprintf(file, "(");
  for (i=1; i<dim; i++)
    fprintf(file, "%s ", clock_name(AT(marx,i,i)));
  fprintf(file, "active)\n");
}

void  pretty_print_matrix(MATRIX marx)
{
  pretty_fprint_matrix(stdout, marx);
}

int  
forward_proj_matrix(MATRIX marx) {
  /* Represents the passage of time (upper bounds are eliminated).
   * Returns the dimension of "marx" (just in case somebody's interested).
   */

  int i, dim;

  dim = matrix_dimension(marx);
  for (i=1; i<dim; i++) {
    AT(marx,i,0) = INFTY_LT;
  }
#ifdef VVERBOSE
  printf("forward_proj_matrix...\n");
  print_matrix(marx);
#endif
  return(dim);
}

int  
canonicalize_matrix(MATRIX marx) {
  /* Returns 0 if "marx" is inconsistent, otherwise the dimension of 
   * "marx" (>1).
   */

  int i, j, k, dim;

  dim = matrix_dimension(marx);
  for (k=0; k<dim; k++)
    for (i=0; i<dim; i++)
      if ((i!=k) && (AT(marx,i,k) != INFTY_LT)) {
        if (is_bound_lt(add_bounds2(AT(marx,i,k), AT(marx,k,i)), ZERO_LE)) {
          /* the constraints represented by the matrix are inconsistent */
          return(0);
        }
        for (j=0; j<dim; j++)
         if ((i!=j) && (j!=k))
          if (AT(marx,k,j) != INFTY_LT)
            if (is_bound_lt(add_bounds2(AT(marx,i,k), AT(marx,k,j)), AT(marx,i,j)))
              AT(marx,i,j) = add_bounds2(AT(marx,i,k), AT(marx,k,j));
      }
#ifdef VVERBOSE
  printf("canonicalize_matrix...\n");
  print_matrix(marx);
#endif
  return(dim);
}

void
relax_matrix(MATRIX marx) {
  int i,j;

  for (j = 1; j < matrix_dimension(marx); j+=1) {
    AT(marx,0,j) = ZERO_LE;
  }
  for (i = 1; i < matrix_dimension(marx); i+=1) {
    for (j = 0; j < matrix_dimension(marx); j+=1) {
      if (i != j) {
        AT(marx,i,j) = INFTY_LT;
      }
    }
  }
}

void
extrapolate_matrix(MATRIX marx) {
  int i,j,dim;
  dim = matrix_dimension(marx);
  for (i = 0; i < dim; i+=1) {
    AT(temp_matrix,i,i) = AT(marx,i,i);
  }
  relax_matrix(temp_matrix);
  for (i = 1; i < dim; i+=1) {
    AT(temp_matrix,i,0) = mk_bound(clock_max_bound[AT(temp_matrix,i,i)],SGN_LE);
  }
  canonicalize_matrix(temp_matrix);
  for (i = 0; i < dim; i+=1) {
    for (j = 0; j < dim; j+=1) {
      if (i != j) {
        if (is_bound_gt(AT(marx,i,j),AT(temp_matrix,i,j))) {
          AT(marx,i,j) = INFTY_LT;
	}       
        else {
          if (is_bound_lt(AT(marx,i,j),compl_bound(AT(temp_matrix,j,i)))) {
            AT(marx,i,j) = compl_bound(AT(temp_matrix,j,i));
	  }
	}
      }
    }
  }
#ifdef VVERBOSE
  printf("extrapolate_matrix...\n");
  print_matrix(marx);
#endif
}

int 
find_clock_index_in_matrix(MATRIX marx, int x) {
  int i;

  if (x == 0) {
    return(0);
  }
  for (i = 1; i < matrix_dimension(marx); i++) {
    if (AT(marx,i,i) == x) {
      return(i);
    }
  } 
  return(-1);
}

void 
atomic_guard_intersect(MATRIX marx, int clk1, int clk2, BOUND_TYPE bound) {
  int i = find_clock_index_in_matrix(marx,clk1);
  int j = find_clock_index_in_matrix(marx,clk2);
  AT(marx,i,j) = min_bound(AT(marx,i,j),bound);
}

void
intersect_lower_bound_matrix(MATRIX marx, int clk, int v) {
  int i = find_clock_index_in_matrix(marx,clk); 
  AT(marx,0,i) = min_bound(AT(marx,0,i),mk_bound(-v,SGN_LE)); 
#ifdef VVERBOSE
  printf("intersect_lower_bound_matrix...\n");
  print_matrix(marx);
#endif
}
 
void 
init_succ_matrix(MATRIX from, MATRIX to) {
  int i,j;
  uchar C2If[N_CLOCKS];  /* Clock to Index of 'from'          */
  uchar It2If[DIM];      /* Index of 'to' to Index of 'from'  */
  memset(to,0,MATRIX_N_BYTES);
  matrix_dimension(to) = n_active_clocks();
  for (i = j = 1; i < N_CLOCKS; i+=1) {
    if (active_clock[i]) {
      if (j >= DIM) {
        printf("Matrix dimension exceeded\n");
        exit(1);
      }
      AT(to,j,j) = i;
      j+=1;
    }
  }

  memset(C2If,0,N_CLOCKS);
  memset(It2If,0,DIM);
  for (i = 1; i < matrix_dimension(from); i+=1) {
    if (active_clock[AT(from,i,i)]) {
      C2If[AT(from,i,i)] = i;
    }
  }
  for (i = 1; i < matrix_dimension(to); i+=1) {
    if (C2If[AT(to,i,i)]) {
      It2If[i] = C2If[AT(to,i,i)];
    }
  }
  for (i = 1; i < matrix_dimension(to); i+=1) {
    for (j = 1; j < matrix_dimension(to); j+=1) {
      if (i != j) {
        if (It2If[i] && It2If[j]) {
          AT(to,i,j) = AT(from,It2If[i],It2If[j]);
        }
        else {
          AT(to,i,j) = INFTY_LT;
        }
      }
    }  
  }
  for (i = 1; i < matrix_dimension(to); i+=1) {
    if (It2If[i]) {
      AT(to,0,i) = AT(from,0,It2If[i]);
      AT(to,i,0) = AT(from,It2If[i],0);
    }
    else {
      AT(to,0,i) = ZERO_LE;
      AT(to,i,0) = INFTY_LT;
    }
  }
#ifdef VVERBOSE
  printf("init_succ_matrix...\n");
  print_matrix(to);
#endif
}

void 
fprint_active_clocks(FILE *f) {
  int i;
  for (i = 0; i < N_CLOCKS; i+=1) {
    if (active_clock[i]) {
      printf("H%d is active\n",i);
    }
    else {
      printf("H%d is not active\n",i);
    }
  }
}

void
print_active_clocks () {
  fprint_active_clocks(stdout);
}

void
sizes (MATRIX m) {
  printf("Matrix (allocated) : %d\n",MATRIX_N_BYTES);
  printf("Matrix (used)      : %d\n",matrix_dimension(m) * 
                                     matrix_dimension(m) * sizeof(BOUND_TYPE));
  printf("active_clock       : %d\n",N_CLOCKS * sizeof(uchar));   
}

void
reset_matrix(MATRIX marx) {
  int i,j;
  for (i = 1; i < matrix_dimension(marx); i+=1) {
    if (reset_clock[AT(marx,i,i)]) {
      AT(marx,0,i) = AT(marx,i,0) = ZERO_LE;
      for (j = 1; j < matrix_dimension(marx); j+=1) {
        if (i != j) {
          AT(marx,i,j) = AT(marx,0,j);
          AT(marx,j,i) = AT(marx,j,0);
        }
      }
    }
  }
#ifdef VVERBOSE
  printf("reset_matrix...\n");
  print_matrix(marx);
#endif
}
/**************************End Matrix************************************/

/********************** End DBMS **********************************/

#define BLANK_MESSAGE 0xffffffff

#define N_PLACES 38

#define MARKING_N_BYTES 5

#define N_CHANNELS 1

#define MAX_N_MIDS 7

#define QSZ 7

#define URGENT_CLOCK 1

#define LABEL_NAME_MAX_N_CHARS 1024

typedef enum {FREE=0, PRE=1, ACCPT=2, POST=3} status_t;

typedef enum {SND=0, RCV=1, COMP=2, GU=3, FP=4, PA=5, AP=6, PF=7} label_type_t;

typedef enum {_CHAN_k=0} chan_id_t;

typedef enum {_CHAN_k_MID_shutdown=0, _CHAN_k_MID_pumpoff=1, _CHAN_k_MID_pumpon=2, _CHAN_k_MID_level=3, _CHAN_k_MID_start=4, _CHAN_k_MID_pump_ready=5, _CHAN_k_MID_sensor_ready=6} _CHAN_k_MID_t;

typedef struct {
  uint _pri;
  uint _dlb;
  uint _dub;
  uint _dlB;
  uint _duB;
} msg_static_t;
  
typedef msg_static_t chan_static_t[MAX_N_MIDS];

typedef chan_static_t net_static_t[N_CHANNELS];

typedef struct {
  ushort value;
  ushort _PAD0     : 3;
  ushort id        : 11;
  status_t status  : 2;
} sidv_t;

typedef struct {
  ushort id;
  ushort value;
} message_t;

#include ".\boiler7_data.c"

typedef struct {
#ifdef MDZN
  uchar        marking[MARKING_N_BYTES];
  data_env_t   env;
  MATRIX       marx;
  sidv_t       sidv[N_CHANNELS];
  message_t    q[QSZ];
#elif defined(MNDZ)
  uchar        marking[MARKING_N_BYTES];
  sidv_t       sidv[N_CHANNELS];
  message_t    q[QSZ];
  data_env_t   env;
  MATRIX       marx;
#elif defined(MNZD)
  uchar        marking[MARKING_N_BYTES];
  sidv_t       sidv[N_CHANNELS];
  message_t    q[QSZ];
  MATRIX       marx;
  data_env_t   env;
#elif defined(MZDN)
  uchar        marking[MARKING_N_BYTES];
  MATRIX       marx;
  data_env_t   env;
  sidv_t       sidv[N_CHANNELS];
  message_t    q[QSZ];
#elif defined(MZND)
  uchar        marking[MARKING_N_BYTES];
  MATRIX       marx;
  sidv_t       sidv[N_CHANNELS];
  message_t    q[QSZ];
  data_env_t   env;
#elif defined(DMNZ)
  data_env_t   env;
  uchar        marking[MARKING_N_BYTES];
  sidv_t       sidv[N_CHANNELS];
  message_t    q[QSZ];
  MATRIX       marx;
#elif defined(DMZN)
  data_env_t   env;
  uchar        marking[MARKING_N_BYTES];
  MATRIX       marx;
  sidv_t       sidv[N_CHANNELS];
  message_t    q[QSZ];
#elif defined(DNMZ)
  data_env_t   env;
  sidv_t       sidv[N_CHANNELS];
  message_t    q[QSZ];
  uchar        marking[MARKING_N_BYTES];
  MATRIX       marx;
#elif defined(DNZM)
  data_env_t   env;
  sidv_t       sidv[N_CHANNELS];
  message_t    q[QSZ];
  MATRIX       marx;
  uchar        marking[MARKING_N_BYTES];
#elif defined(DZMN)
  data_env_t   env;
  MATRIX       marx;
  uchar        marking[MARKING_N_BYTES];
  sidv_t       sidv[N_CHANNELS];
  message_t    q[QSZ];
#elif defined(DZNM)
  data_env_t   env;
  MATRIX       marx;
  sidv_t       sidv[N_CHANNELS];
  message_t    q[QSZ];
  uchar        marking[MARKING_N_BYTES];
#elif defined(NMDZ)
  sidv_t       sidv[N_CHANNELS];
  message_t    q[QSZ];
  uchar        marking[MARKING_N_BYTES];
  data_env_t   env;
  MATRIX       marx;
#elif defined(NMZD)
  sidv_t       sidv[N_CHANNELS];
  message_t    q[QSZ];
  uchar        marking[MARKING_N_BYTES];
  MATRIX       marx;
  data_env_t   env;
#elif defined(NDMZ)
  sidv_t       sidv[N_CHANNELS];
  message_t    q[QSZ];
  data_env_t   env;
  uchar        marking[MARKING_N_BYTES];
  MATRIX       marx;
#elif defined(NDZM)
  sidv_t       sidv[N_CHANNELS];
  message_t    q[QSZ];
  data_env_t   env;
  MATRIX       marx;
  uchar        marking[MARKING_N_BYTES];
#elif defined(NZMD)
  sidv_t       sidv[N_CHANNELS];
  message_t    q[QSZ];
  MATRIX       marx;
  uchar        marking[MARKING_N_BYTES];
  data_env_t   env;
#elif defined(NZDM)
  sidv_t       sidv[N_CHANNELS];
  message_t    q[QSZ];
  MATRIX       marx;
  data_env_t   env;
  uchar        marking[MARKING_N_BYTES];
#elif defined(ZMDN)
  MATRIX       marx;
  uchar        marking[MARKING_N_BYTES];
  data_env_t   env;
  sidv_t       sidv[N_CHANNELS];
  message_t    q[QSZ];
#elif defined(ZMND)
  MATRIX       marx;
  uchar        marking[MARKING_N_BYTES];
  sidv_t       sidv[N_CHANNELS];
  message_t    q[QSZ];
  data_env_t   env;
#elif defined(ZDMN)
  MATRIX       marx;
  data_env_t   env;
  uchar        marking[MARKING_N_BYTES];
  sidv_t       sidv[N_CHANNELS];
  message_t    q[QSZ];
#elif defined(ZDNM)
  MATRIX       marx;
  data_env_t   env;
  sidv_t       sidv[N_CHANNELS];
  message_t    q[QSZ];
  uchar        marking[MARKING_N_BYTES];
#elif defined(ZNMD)
  MATRIX       marx;
  sidv_t       sidv[N_CHANNELS];
  message_t    q[QSZ];
  uchar        marking[MARKING_N_BYTES];
  data_env_t   env;
#elif defined(ZNDM)
  MATRIX       marx;
  sidv_t       sidv[N_CHANNELS];
  message_t    q[QSZ];
  data_env_t   env;
  uchar        marking[MARKING_N_BYTES];
#else
  uchar        marking[MARKING_N_BYTES];
  data_env_t   env;
  sidv_t       sidv[N_CHANNELS];
  message_t    q[QSZ];
  MATRIX       marx;
#endif
} state_vector_t;

typedef struct {
  label_type_t type;
  ushort       k;
  ushort       i;
  ushort       v;
  char         name[LABEL_NAME_MAX_N_CHARS];
  short        clock;
  uint         bound;
  short        resets[N_CLOCKS];
} label_t;

typedef struct {
  short      clock;
  BOUND_TYPE bound;
} upper_bound_t;

typedef void (*state_operator_t)(state_vector_t *, label_t *, state_vector_t *);

#define pri(k,i) (net_static[k][i]._pri)
#define dlb(k,i) (net_static[k][i]._dlb)
#define dub(k,i) (net_static[k][i]._dub)
#define dlB(k,i) (net_static[k][i]._dlB)
#define duB(k,i) (net_static[k][i]._duB)

static net_static_t net_static =
{{{1, 43, 53, 10, 12}, {2, 43, 53, 10, 12}, {3, 43, 53, 10, 12}, {4, 53, 63, 10, 12}, {5, 43, 53, 10, 12}, {6, 43, 53, 10, 12}, {7, 43, 53, 10, 12}}};

static short n_mids_per_chan[N_CHANNELS] = {7};

static short q_max_n[N_CHANNELS] = {7};

static short q_offset[N_CHANNELS] = {0};

static int net_clocks[N_CHANNELS] = {2};

static upper_bound_t tinv[N_PLACES] = {
  {-1,0},
  {-1,0},
  {3, mk_bound(350, SGN_LE)},
  {1, ZERO_LE},
  {12, mk_bound(5100, SGN_LE)},
  {-1,0},
  {3, mk_bound(75, SGN_LE)},
  {1, ZERO_LE},
  {10, mk_bound(10250, SGN_LE)},
  {-1,0},
  {4, mk_bound(1500, SGN_LE)},
  {1, ZERO_LE},
  {8, mk_bound(5100, SGN_LE)},
  {-1,0},
  {-1,0},
  {4, mk_bound(300, SGN_LE)},
  {-1,0},
  {4, mk_bound(300, SGN_LE)},
  {-1,0},
  {6, mk_bound(300, SGN_LE)},
  {5, mk_bound(500, SGN_LE)},
  {-1,0},
  {-1,0},
  {-1,0},
  {-1,0},
  {1, ZERO_LE},
  {-1,0},
  {5, mk_bound(15, SGN_LE)},
  {1, ZERO_LE},
  {1, ZERO_LE},
  {5, mk_bound(15, SGN_LE)},
  {1, ZERO_LE},
  {1, ZERO_LE},
  {1, ZERO_LE},
  {1, ZERO_LE},
  {1, ZERO_LE},
  {5, mk_bound(15500, SGN_LE)},
  {1, ZERO_LE}
};

typedef int (*PRED_TYPE)(data_env_t *);

static PRED_TYPE PRED[N_PLACES] = {
  PRED___false,
  PRED___false,
  PRED___true,
  PRED___true,
  PRED___true,
  PRED___false,
  PRED___true,
  PRED___true,
  PRED___true,
  PRED___false,
  PRED___true,
  PRED___true,
  PRED___true,
  PRED___false,
  PRED___false,
  PRED___true,
  PRED___false,
  PRED___true,
  PRED___false,
  PRED___true,
  PRED___true,
  PRED___false,
  PRED___false,
  PRED___false,
  PRED___false,
  PRED___true,
  PRED___false,
  PRED___true,
  PRED___true,
  PRED_HighLevel,
  PRED___true,
  PRED_notHighLevel,
  PRED___true,
  PRED_LowLevel,
  PRED___true,
  PRED_notLowLevel,
  PRED___true,
  PRED___true
};

#ifdef BFS
static queue_t *to_do;
#else
static stack_t *to_do;
#endif
static stack_t *data;
static int global_state_number = 0;
static int global_transition_number = 0;
static int global_invariant_violations = 0;

#ifdef SIM
static state_vector_t global_state_array[100];
#endif
#ifndef MA
Hash_table_t state_table_data;
Hash_table_t *state_table = &state_table_data;
#endif
#ifdef VDIM
static int global_matrix_number = 0;
Hash_table_t marx_table_data;
Hash_table_t *marx_table = &marx_table_data;
#endif

void fprint_marking(FILE *f, state_vector_t *svec) {
  int i;

  for (i = 0; i < MARKING_N_BYTES; i++) {
    if (svec->marking[i] & 0x80) {
      fprintf(f,"%d ",i * 8);
    }
    if (svec->marking[i] & 0x40) {
      fprintf(f,"%d ",i * 8 + 1);
    }
    if (svec->marking[i] & 0x20) {
      fprintf(f,"%d ",i * 8 + 2);
    }
    if (svec->marking[i] & 0x10) {
      fprintf(f,"%d ",i * 8 + 3);
    }
    if (svec->marking[i] & 0x08) {
      fprintf(f,"%d ",i * 8 + 4);
    }
    if (svec->marking[i] & 0x04) {
      fprintf(f,"%d ",i * 8 + 5);
    }
    if (svec->marking[i] & 0x02) {
      fprintf(f,"%d ",i * 8 + 6);
    }
    if (svec->marking[i] & 0x01) {
      fprintf(f,"%d ",i * 8 + 7);
    }
  }
  fprintf(f,"\n");
}

void print_marking(state_vector_t *svec) {
  fprint_marking(stdout,svec);
}

void fprint_net_static (FILE *f) {
  uint k, i;

  for (k=0; k < N_CHANNELS; k++) {
    int nids = n_mids_per_chan[k];
    for (i=0; i < nids; i++) {
      fprintf(f,"%6d  %6d  %6d  %6d  %6d\n",
        pri(k,i),dlb(k,i),dub(k,i),dlB(k,i),duB(k,i));
    }
  }
}

void print_net_static() {
  fprint_net_static(stdout);
}

void 
fprint_status(FILE *f, status_t status) {
  switch (status) {
  case FREE : 
    fprintf(f,"FREE"); break;
  case PRE :
    fprintf(f,"PRE"); break;
  case ACCPT :
    fprintf(f,"ACCPT"); break;
  case POST :
    fprintf(f,"POST"); break;
  default :
    fprintf(f,"error : unknown status");
  }
}

void print_status(status_t status) {
  fprint_status(stdout,status);
}

void
fprint_sidv(FILE *f, state_vector_t * svec, ushort k) {
  status_t st = svec->sidv[k].status;
  fprint_status(f,st);
  if (st != FREE) {
    fprintf(f,"(%d.%d)",svec->sidv[k].id,svec->sidv[k].value);
  }
}

void 
print_sidv(state_vector_t * svec, ushort k) {
  fprint_sidv(stdout,svec,k);
}

void fprint_message(FILE *f, message_t m) {
  if ((*(uint *)&m) != BLANK_MESSAGE) {
    fprintf(f,"%d.%d", m.id, m.value);
  }
  else {
    fprintf(f,"_");
  }
}

void print_message(message_t m) {
  fprint_message(stdout, m);
}

void 
fprint_q(FILE *f, state_vector_t *svec, ushort k) {
  message_t *q, *e;

  q = svec->q + q_offset[k];
  e = q + q_max_n[k];
  while (q < e) {
    fprint_message(f,*q);
    fprintf(f," ");
    q++;
  } 
}

void print_q(state_vector_t *svec, ushort k) {
  fprint_q(stdout,svec,k);
}

void fprint_net_dynamic(FILE *f, state_vector_t *svec) {
  int k;

  for (k = 0; k < N_CHANNELS; k++) {
    fprintf(f,"%6d : ",k);
    fprint_sidv(f,svec,k);
    fprintf(f,"\n  ");
    fprint_q(f,svec,k);
    fprintf(f,"\n\n");
  }
}

void
print_net_dynamic(state_vector_t *svec) {
  fprint_net_dynamic(stdout,svec);
}

void
fprint_label(FILE *f, label_t *lab) {

  switch (lab->type) {
  case SND:
    fprintf(f,"SND_%d_%d_%d",lab->k,lab->i,lab->v);
    break;
  case RCV:
    fprintf(f,"RCV_%d_%d_%d",lab->k,lab->i,lab->v);
    break;
  case COMP:
    fprintf(f,"%s", lab->name);
    break;
  case GU:
    fprintf(f,"%s", lab->name);
    break;
  case FP:
    fprintf(f,"FP_%d_%d_%d",lab->k,lab->i,lab->v);
    break;
  case PA:
    fprintf(f,"PA_%d_%d_%d",lab->k,lab->i,lab->v);
    break;
  case AP:
    fprintf(f,"AP_%d",lab->k);
    break;
  case PF:
    fprintf(f,"PF_%d",lab->k);
    break;
  default:
    uerror("unexpected label type");
    break;
  }
}

void 
print_label(label_t *lab) {
  fprint_label(stdout,lab);
}

void 
fprint_state (FILE *f, state_vector_t *svec) {
  fprint_marking(f,svec);
  fprint_net_dynamic(f,svec);
  fprint_matrix(f,svec->marx);
}

void
print_state (state_vector_t *svec) {
 fprint_state(stdout,svec);
}

void 
fprint_state_vector_bytes(FILE *f, state_vector_t *svec) {
  int i;
  for (i = 0; i < sizeof(state_vector_t); i+=1) {
    fprintf(f,"%02x ", *((uchar *)svec + i));
  }
}

void print_state_vector_bytes(state_vector_t *svec) {
  fprint_state_vector_bytes(stdout,svec);
}

void
fprint_state_vector_boundaries(FILE *f, state_vector_t *svec) {
  fprintf(f, "State vector boundaries: marking  %d, env %d, sidv %d, q %d, marx %d\n",
    ((ulong)&(svec->marking) - (ulong)svec), 
    ((ulong)&(svec->env) - (ulong)svec), 
    ((ulong)&(svec->sidv) - (ulong)svec),
    ((ulong)&(svec->q) - (ulong)svec),
    ((ulong)&(svec->marx) - (ulong)svec));
}

void
print_state_vector_boundaries(state_vector_t *svec) {
  fprint_state_vector_boundaries(stdout,svec);
}

void 
q_insert(state_vector_t *svec, ushort k, ushort i, ushort v) {
  message_t *q, *p, *b;

  q = b = svec->q + q_offset[k];
  p = q + q_max_n[k];
  while ((*(uint *)b) != BLANK_MESSAGE) {
    if (b->id == i) {
      b->value = v;
      return;
    }
    if (++b == p) {
      printf("Queue full -- channel %d\n",k); wrapup(0);
    }
  }
  p = q;
  while (i > p->id) {
    p++;
  }
  while (b > p) {
    *b = *(b - 1);
    b--;
  }
  b->id = i; b->value = v;
}


/* returns 0 if q is empty or status not free and hence no message 
     transmission begun, 
   returns 1 otherwise
*/
int 
q_trans(state_vector_t *svec, ushort k) {
  message_t *q = svec->q + q_offset[k];
  message_t *e = q + q_max_n[k];
  if (((*(uint *)q) == BLANK_MESSAGE) || (svec->sidv[k].status != FREE)) {
    return 0;
  }
  else {
    message_t *r = q + 1;
    svec->sidv[k].status = PRE;
    svec->sidv[k].id = q->id;
    svec->sidv[k].value = q->value;
    while ((r < e) && ((*(uint *)r) != BLANK_MESSAGE)) {
      *q++ = *r++; 
    }
    *(uint *)q = BLANK_MESSAGE;
    return 1;
  }  
}

#ifdef NOACT
void
set_active_clocks(state_vector_t *svec) {
  memset(active_clock,1,N_CLOCKS);
}
#else
void
set_active_clocks(state_vector_t *svec) {
  int i,p;
  memset(active_clock,0,N_CLOCKS);
  active_clock[0] = 1;
  for (i = 0; i < N_CHANNELS; i++) {
    switch (svec->sidv[i].status) {
    case FREE : {
      message_t *q = svec->q + q_offset[i];
      if ((*(uint *)q) != BLANK_MESSAGE) {
        active_clock[URGENT_CLOCK] = 1;
      }
      break;
    }
    case PRE :
      active_clock[net_clocks[i]] = 1;
      break;
    case ACCPT :
      active_clock[URGENT_CLOCK] = 1;
      break;
    case POST :
      active_clock[net_clocks[i]] = 1;
      break;
    default :
      Uerror("Error in network status");
      break;
    }
  }

  for (i = 0; i < MARKING_N_BYTES; i++) {
    if (svec->marking[i]) {
      p = i * 8;
      if ((svec->marking[i] & 0x80) && (PRED[p](&svec->env))) {
        active_clock[tinv[p].clock] = 1;
      }
      p += 1;
      if ((svec->marking[i] & 0x40) && (PRED[p](&svec->env))) {
        active_clock[tinv[p].clock] = 1;
      }
      p += 1;
      if ((svec->marking[i] & 0x20) && (PRED[p](&svec->env))) {
        active_clock[tinv[p].clock] = 1;
      }
      p += 1;
      if ((svec->marking[i] & 0x10) && (PRED[p](&svec->env))) {
        active_clock[tinv[p].clock] = 1;
      }
      p += 1;
      if ((svec->marking[i] & 0x08) && (PRED[p](&svec->env))) {
        active_clock[tinv[p].clock] = 1;
      }
      p += 1;
      if ((svec->marking[i] & 0x04) && (PRED[p](&svec->env))) {
        active_clock[tinv[p].clock] = 1;
      }
      p += 1;
      if ((svec->marking[i] & 0x02) && (PRED[p](&svec->env))) {
        active_clock[tinv[p].clock] = 1;
      }
      p += 1;
      if ((svec->marking[i] & 0x01) && (PRED[p](&svec->env))) {
        active_clock[tinv[p].clock] = 1;
      }
    }
  }
}
#endif

void invariant_violation() {
  global_invariant_violations += 1;
#ifdef INVARIANT_VIOLATIONS
  printf("State %d: Invariant violated\n", global_state_number);
#endif
}

#ifdef VDIM
MATRIX
hstore_matrix(MATRIX marx) {
  int dim = matrix_dimension(marx);
  if (is_trivial_matrix(marx)) {
    return NULL;
  }
  else {
    if (!hstore(marx_table, (char *)marx,dim*dim*sizeof(BOUND_TYPE))) {
      global_matrix_number += 1;
    }
    return ((MATRIX)(marx_table->hstored));
  }
}
#endif

void
intersect_invariant_matrix(state_vector_t *svec, MATRIX marx) {
  int i,k,c,p;
  uchar C2I[N_CLOCKS];  /* Clock to Index */
  memset(C2I,0,N_CLOCKS);
  for (i = 1; i < matrix_dimension(marx); i+=1) {
    C2I[AT(marx,i,i)] = i;
  }  
  for (k = 0; k < N_CHANNELS; k++) {
    switch (svec->sidv[k].status) {
    case FREE : {
      message_t *q = svec->q + q_offset[k];
      if ((*(uint *)q) != BLANK_MESSAGE) {
        c = C2I[URGENT_CLOCK];
        AT(marx,c,0) = min_bound(AT(marx,c,0),ZERO_LE);
      }
      break;
    }
    case PRE :
      c = C2I[net_clocks[k]];
      AT(marx,c,0) = min_bound(AT(marx,c,0),
                                     mk_bound(dub(k,svec->sidv[k].id),SGN_LE));
      break;
    case ACCPT :
      c = C2I[URGENT_CLOCK];
      AT(marx,c,0) = min_bound(AT(marx,c,0),ZERO_LE);
      break;
    case POST :
      c = C2I[net_clocks[k]];
      AT(marx,c,0) = min_bound(AT(marx,c,0),
                                     mk_bound(duB(k,svec->sidv[k].id),SGN_LE));
      break;
    }
  }

  for (i = 0; i < MARKING_N_BYTES; i++) {
    if (svec->marking[i]) {
      p = i * 8;
      if ((svec->marking[i] & 0x80) && (PRED[p](&svec->env))) {
        c = C2I[tinv[p].clock];
        AT(marx,c,0) = min_bound(AT(marx,c,0),tinv[p].bound);
      }
      p += 1;
      if ((svec->marking[i] & 0x40) && (PRED[p](&svec->env))) {
        c = C2I[tinv[p].clock];
        AT(marx,c,0) = min_bound(AT(marx,c,0),tinv[p].bound);
      }
      p += 1;
      if ((svec->marking[i] & 0x20) && (PRED[p](&svec->env))) {
        c = C2I[tinv[p].clock];
        AT(marx,c,0) = min_bound(AT(marx,c,0),tinv[p].bound);
      }
      p += 1;
      if ((svec->marking[i] & 0x10) && (PRED[p](&svec->env))) {
        c = C2I[tinv[p].clock];
        AT(marx,c,0) = min_bound(AT(marx,c,0),tinv[p].bound);
      }
      p += 1;
      if ((svec->marking[i] & 0x08) && (PRED[p](&svec->env))) {
        c = C2I[tinv[p].clock];
        AT(marx,c,0) = min_bound(AT(marx,c,0),tinv[p].bound);
      }
      p += 1;
      if ((svec->marking[i] & 0x04) && (PRED[p](&svec->env))) {
        c = C2I[tinv[p].clock];
        AT(marx,c,0) = min_bound(AT(marx,c,0),tinv[p].bound);
      }
      p += 1;
      if ((svec->marking[i] & 0x02) && (PRED[p](&svec->env))) {
        c = C2I[tinv[p].clock];
        AT(marx,c,0) = min_bound(AT(marx,c,0),tinv[p].bound);
      }
      p += 1;
      if ((svec->marking[i] & 0x01) && (PRED[p](&svec->env))) {
        c = C2I[tinv[p].clock];
        AT(marx,c,0) = min_bound(AT(marx,c,0),tinv[p].bound);
      }
    }
  }
#ifdef VVERBOSE
  printf("intersect_invariant_matrix...\n");
  print_matrix(marx);
#endif
}

#define size_state() (sizeof(state_vector_t))

void
start_state(state_vector_t *svec) {
  uchar init_marking[MARKING_N_BYTES] = {0x20, 0x20, 0x08, 0x00, 0x00};
  memcpy(&(svec->marking),&init_marking,MARKING_N_BYTES);
  memset(&(svec->q), 0xff, QSZ * sizeof(message_t)); 
  set_active_clocks(svec);
  memcpy(reset_clock,active_clock,N_CLOCKS);
  matrix_dimension(temp_matrix) = 0;
  init_succ_matrix(temp_matrix,new_matrix);
  reset_matrix(new_matrix);
  forward_proj_matrix(new_matrix);
  intersect_invariant_matrix(svec,new_matrix);
  if (!canonicalize_matrix(new_matrix)) {
    invariant_violation();
  }
  else {
    extrapolate_matrix(new_matrix);
#ifdef VDIM
    svec->marx = hstore_matrix(new_matrix);
#else
    memcpy(svec->marx, new_matrix, MATRIX_N_BYTES); 
#endif
  }   
}

void 
iterate_state(state_vector_t *s1, label_t *lab, 
              state_vector_t *s2, state_operator_t doit) {

  int i;
  uint k;
  uchar marking;
  int stopped[N_CHANNELS] = {0};    
  BOUND_TYPE s1_matrix[DIM*DIM];

  marking = s1->marking[0];
  if (marking != 0) {
    if (marking & 0x80) {
      uerror("tick shouldn't happen");
    }
    if (marking & 0x40) {
      /* idle doesn't generate any transitions */
    }
    if (marking & 0x20) { /* trigger 2 */
        memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
        intersect_lower_bound_matrix(s1_matrix, 3, 300);
        if (canonicalize_matrix(s1_matrix)) {
          char vw[MARKING_N_BYTES] = {0x20, 0x00, 0x00, 0x00, 0x00};
          char t[MARKING_N_BYTES] = {0x1c, 0x00, 0x00, 0x00, 0x00};
          memcpy((char *)s2, (char *)s1, size_state()); 
          for (i = 0; i < MARKING_N_BYTES; i++) {
            s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
          }
          {
            uchar r[N_CLOCKS] = {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1};
            memcpy(reset_clock,r,N_CLOCKS);
          }
          lab->type = COMP; strcpy(lab->name,"OP_InitSensor");
          OP_InitSensor(&(s1->env),data);
          while (data->top->nxtElem) {
            pop(data,&(s2->env));
            set_active_clocks(s2);
            init_succ_matrix(s1_matrix,new_matrix);
            reset_matrix(new_matrix);
            forward_proj_matrix(new_matrix);
            intersect_invariant_matrix(s2,new_matrix);
            if (!canonicalize_matrix(new_matrix)) {
              invariant_violation();
            }
            else {
              extrapolate_matrix(new_matrix); 
#ifdef VDIM
              s2->marx = hstore_matrix(new_matrix); 
#else
              memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
              doit(s1,lab,s2);
            }
          }
        }
    }
    if (marking & 0x10) { /* trigger 3 */
          char vw[MARKING_N_BYTES] = {0x10, 0x00, 0x00, 0x00, 0x00};
          char t[MARKING_N_BYTES] = {0x40, 0x00, 0x00, 0x00, 0x00};
          memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
          memcpy((char *)s2, (char *)s1, size_state()); 
          for (i = 0; i < MARKING_N_BYTES; i++) {
            s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
          }
          {
            uchar r[N_CLOCKS] = {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
            memcpy(reset_clock,r,N_CLOCKS);
          }
          q_insert(s2,_CHAN_k,_CHAN_k_MID_sensor_ready,s1->env._VAR__);
          set_active_clocks(s2);
          init_succ_matrix(s1_matrix,new_matrix);
          reset_matrix(new_matrix);
          forward_proj_matrix(new_matrix);
          intersect_invariant_matrix(s2,new_matrix);
          if (!canonicalize_matrix(new_matrix)) {
            invariant_violation();
          }
          else {
            extrapolate_matrix(new_matrix);
#ifdef VDIM
            s2->marx = hstore_matrix(new_matrix); 
#else
            memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
            lab->type = SND; lab->k = _CHAN_k;
            lab->i = _CHAN_k_MID_sensor_ready; lab->v = s1->env._VAR__;
            doit(s1,lab,s2);
          }
    }
    if (marking & 0x08) { /* trigger 4 */
        memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
        intersect_lower_bound_matrix(s1_matrix, 12, 5000);
        if (canonicalize_matrix(s1_matrix)) {
          char vw[MARKING_N_BYTES] = {0x58, 0x00, 0x00, 0x00, 0x00};
          char t[MARKING_N_BYTES] = {0x18, 0x00, 0x00, 0x00, 0x00};
          memcpy((char *)s2, (char *)s1, size_state()); 
          for (i = 0; i < MARKING_N_BYTES; i++) {
            s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
          }
          {
            uchar r[N_CLOCKS] = {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1};
            memcpy(reset_clock,r,N_CLOCKS);
          }
          lab->type = COMP; strcpy(lab->name,"OP_WL_ReadyPeriod");
          OP_WL_ReadyPeriod(&(s1->env),data);
          while (data->top->nxtElem) {
            pop(data,&(s2->env));
            set_active_clocks(s2);
            init_succ_matrix(s1_matrix,new_matrix);
            reset_matrix(new_matrix);
            forward_proj_matrix(new_matrix);
            intersect_invariant_matrix(s2,new_matrix);
            if (!canonicalize_matrix(new_matrix)) {
              invariant_violation();
            }
            else {
              extrapolate_matrix(new_matrix); 
#ifdef VDIM
              s2->marx = hstore_matrix(new_matrix); 
#else
              memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
              doit(s1,lab,s2);
            }
          }
        }
    }
    if (marking & 0x04) { /* trigger 5 */
      if ((s1->sidv[_CHAN_k].status == ACCPT) && (s1->sidv[_CHAN_k].id == _CHAN_k_MID_start)) {
          char vw[MARKING_N_BYTES] = {0x5c, 0x00, 0x00, 0x00, 0x00};
          char t[MARKING_N_BYTES] = {0x02, 0xc0, 0x00, 0x00, 0x00};
          memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
          memcpy((char *)s2, (char *)s1, size_state()); 
          for (i = 0; i < MARKING_N_BYTES; i++) {
            s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
          }
          s2->env._VAR__ = s1->sidv[_CHAN_k].value;
          {
            uchar r[N_CLOCKS] = {1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0};
            memcpy(reset_clock,r,N_CLOCKS);
          }
          set_active_clocks(s2);
          init_succ_matrix(s1_matrix,new_matrix);
          reset_matrix(new_matrix);
          forward_proj_matrix(new_matrix);
          intersect_invariant_matrix(s2,new_matrix);
          if (!canonicalize_matrix(new_matrix)) {
            invariant_violation();
          }
          else {
            extrapolate_matrix(new_matrix); 
#ifdef VDIM
            s2->marx = hstore_matrix(new_matrix); 
#else
            memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
            lab->type = RCV; lab->k = _CHAN_k;
            lab->i = _CHAN_k_MID_start; lab->v = s1->sidv[_CHAN_k].value;
            stopped[_CHAN_k] = 1;
            doit(s1,lab,s2);
          }
      }
    }
    if (marking & 0x02) { /* trigger 6 */
        memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
        intersect_lower_bound_matrix(s1_matrix, 3, 50);
        if (canonicalize_matrix(s1_matrix)) {
          char vw[MARKING_N_BYTES] = {0x02, 0x00, 0x00, 0x00, 0x00};
          char t[MARKING_N_BYTES] = {0x01, 0x00, 0x00, 0x00, 0x00};
          memcpy((char *)s2, (char *)s1, size_state()); 
          for (i = 0; i < MARKING_N_BYTES; i++) {
            s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
          }
          {
            uchar r[N_CLOCKS] = {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
            memcpy(reset_clock,r,N_CLOCKS);
          }
          lab->type = COMP; strcpy(lab->name,"OP_ReadWaterLevel");
          OP_ReadWaterLevel(&(s1->env),data);
          while (data->top->nxtElem) {
            pop(data,&(s2->env));
            set_active_clocks(s2);
            init_succ_matrix(s1_matrix,new_matrix);
            reset_matrix(new_matrix);
            forward_proj_matrix(new_matrix);
            intersect_invariant_matrix(s2,new_matrix);
            if (!canonicalize_matrix(new_matrix)) {
              invariant_violation();
            }
            else {
              extrapolate_matrix(new_matrix); 
#ifdef VDIM
              s2->marx = hstore_matrix(new_matrix); 
#else
              memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
              doit(s1,lab,s2);
            }
          }
        }
    }
    if (marking & 0x01) { /* trigger 7 */
          char vw[MARKING_N_BYTES] = {0x01, 0x00, 0x00, 0x00, 0x00};
          char t[MARKING_N_BYTES] = {0x40, 0x00, 0x00, 0x00, 0x00};
          memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
          memcpy((char *)s2, (char *)s1, size_state()); 
          for (i = 0; i < MARKING_N_BYTES; i++) {
            s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
          }
          {
            uchar r[N_CLOCKS] = {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
            memcpy(reset_clock,r,N_CLOCKS);
          }
          q_insert(s2,_CHAN_k,_CHAN_k_MID_level,s1->env._VAR_w1);
          set_active_clocks(s2);
          init_succ_matrix(s1_matrix,new_matrix);
          reset_matrix(new_matrix);
          forward_proj_matrix(new_matrix);
          intersect_invariant_matrix(s2,new_matrix);
          if (!canonicalize_matrix(new_matrix)) {
            invariant_violation();
          }
          else {
            extrapolate_matrix(new_matrix);
#ifdef VDIM
            s2->marx = hstore_matrix(new_matrix); 
#else
            memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
            lab->type = SND; lab->k = _CHAN_k;
            lab->i = _CHAN_k_MID_level; lab->v = s1->env._VAR_w1;
            doit(s1,lab,s2);
          }
    }
  }

  marking = s1->marking[1];
  if (marking != 0) {
    if (marking & 0x80) { /* trigger 8 */
        memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
        intersect_lower_bound_matrix(s1_matrix, 10, 10000);
        if (canonicalize_matrix(s1_matrix)) {
          char vw[MARKING_N_BYTES] = {0x43, 0x80, 0x00, 0x00, 0x00};
          char t[MARKING_N_BYTES] = {0x02, 0x80, 0x00, 0x00, 0x00};
          memcpy((char *)s2, (char *)s1, size_state()); 
          for (i = 0; i < MARKING_N_BYTES; i++) {
            s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
          }
          {
            uchar r[N_CLOCKS] = {1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0};
            memcpy(reset_clock,r,N_CLOCKS);
          }
          lab->type = COMP; strcpy(lab->name,"OP_WL_NormalPeriod");
          OP_WL_NormalPeriod(&(s1->env),data);
          while (data->top->nxtElem) {
            pop(data,&(s2->env));
            set_active_clocks(s2);
            init_succ_matrix(s1_matrix,new_matrix);
            reset_matrix(new_matrix);
            forward_proj_matrix(new_matrix);
            intersect_invariant_matrix(s2,new_matrix);
            if (!canonicalize_matrix(new_matrix)) {
              invariant_violation();
            }
            else {
              extrapolate_matrix(new_matrix); 
#ifdef VDIM
              s2->marx = hstore_matrix(new_matrix); 
#else
              memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
              doit(s1,lab,s2);
            }
          }
        }
    }
    if (marking & 0x40) { /* trigger 9 */
      if ((s1->sidv[_CHAN_k].status == ACCPT) && (s1->sidv[_CHAN_k].id == _CHAN_k_MID_shutdown)) {
          char vw[MARKING_N_BYTES] = {0x43, 0xc0, 0x00, 0x00, 0x00};
          char t[MARKING_N_BYTES] = {0x40, 0x00, 0x00, 0x00, 0x00};
          memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
          memcpy((char *)s2, (char *)s1, size_state()); 
          for (i = 0; i < MARKING_N_BYTES; i++) {
            s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
          }
          s2->env._VAR__ = s1->sidv[_CHAN_k].value;
          {
            uchar r[N_CLOCKS] = {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
            memcpy(reset_clock,r,N_CLOCKS);
          }
          set_active_clocks(s2);
          init_succ_matrix(s1_matrix,new_matrix);
          reset_matrix(new_matrix);
          forward_proj_matrix(new_matrix);
          intersect_invariant_matrix(s2,new_matrix);
          if (!canonicalize_matrix(new_matrix)) {
            invariant_violation();
          }
          else {
            extrapolate_matrix(new_matrix); 
#ifdef VDIM
            s2->marx = hstore_matrix(new_matrix); 
#else
            memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
            lab->type = RCV; lab->k = _CHAN_k;
            lab->i = _CHAN_k_MID_shutdown; lab->v = s1->sidv[_CHAN_k].value;
            stopped[_CHAN_k] = 1;
            doit(s1,lab,s2);
          }
      }
    }
    if (marking & 0x20) { /* trigger 10 */
        memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
        intersect_lower_bound_matrix(s1_matrix, 4, 250);
        if (canonicalize_matrix(s1_matrix)) {
          char vw[MARKING_N_BYTES] = {0x00, 0x20, 0x00, 0x00, 0x00};
          char t[MARKING_N_BYTES] = {0x00, 0x1c, 0x00, 0x00, 0x00};
          memcpy((char *)s2, (char *)s1, size_state()); 
          for (i = 0; i < MARKING_N_BYTES; i++) {
            s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
          }
          {
            uchar r[N_CLOCKS] = {1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0};
            memcpy(reset_clock,r,N_CLOCKS);
          }
          lab->type = COMP; strcpy(lab->name,"OP_InitPump");
          OP_InitPump(&(s1->env),data);
          while (data->top->nxtElem) {
            pop(data,&(s2->env));
            set_active_clocks(s2);
            init_succ_matrix(s1_matrix,new_matrix);
            reset_matrix(new_matrix);
            forward_proj_matrix(new_matrix);
            intersect_invariant_matrix(s2,new_matrix);
            if (!canonicalize_matrix(new_matrix)) {
              invariant_violation();
            }
            else {
              extrapolate_matrix(new_matrix); 
#ifdef VDIM
              s2->marx = hstore_matrix(new_matrix); 
#else
              memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
              doit(s1,lab,s2);
            }
          }
        }
    }
    if (marking & 0x10) { /* trigger 11 */
          char vw[MARKING_N_BYTES] = {0x00, 0x10, 0x00, 0x00, 0x00};
          char t[MARKING_N_BYTES] = {0x40, 0x00, 0x00, 0x00, 0x00};
          memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
          memcpy((char *)s2, (char *)s1, size_state()); 
          for (i = 0; i < MARKING_N_BYTES; i++) {
            s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
          }
          {
            uchar r[N_CLOCKS] = {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
            memcpy(reset_clock,r,N_CLOCKS);
          }
          q_insert(s2,_CHAN_k,_CHAN_k_MID_pump_ready,s1->env._VAR__);
          set_active_clocks(s2);
          init_succ_matrix(s1_matrix,new_matrix);
          reset_matrix(new_matrix);
          forward_proj_matrix(new_matrix);
          intersect_invariant_matrix(s2,new_matrix);
          if (!canonicalize_matrix(new_matrix)) {
            invariant_violation();
          }
          else {
            extrapolate_matrix(new_matrix);
#ifdef VDIM
            s2->marx = hstore_matrix(new_matrix); 
#else
            memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
            lab->type = SND; lab->k = _CHAN_k;
            lab->i = _CHAN_k_MID_pump_ready; lab->v = s1->env._VAR__;
            doit(s1,lab,s2);
          }
    }
    if (marking & 0x08) { /* trigger 12 */
        memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
        intersect_lower_bound_matrix(s1_matrix, 8, 5000);
        if (canonicalize_matrix(s1_matrix)) {
          char vw[MARKING_N_BYTES] = {0x40, 0x18, 0x00, 0x00, 0x00};
          char t[MARKING_N_BYTES] = {0x00, 0x18, 0x00, 0x00, 0x00};
          memcpy((char *)s2, (char *)s1, size_state()); 
          for (i = 0; i < MARKING_N_BYTES; i++) {
            s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
          }
          {
            uchar r[N_CLOCKS] = {1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0};
            memcpy(reset_clock,r,N_CLOCKS);
          }
          lab->type = COMP; strcpy(lab->name,"OP_P_ReadyPeriod");
          OP_P_ReadyPeriod(&(s1->env),data);
          while (data->top->nxtElem) {
            pop(data,&(s2->env));
            set_active_clocks(s2);
            init_succ_matrix(s1_matrix,new_matrix);
            reset_matrix(new_matrix);
            forward_proj_matrix(new_matrix);
            intersect_invariant_matrix(s2,new_matrix);
            if (!canonicalize_matrix(new_matrix)) {
              invariant_violation();
            }
            else {
              extrapolate_matrix(new_matrix); 
#ifdef VDIM
              s2->marx = hstore_matrix(new_matrix); 
#else
              memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
              doit(s1,lab,s2);
            }
          }
        }
    }
    if (marking & 0x04) { /* trigger 13 */
      if ((s1->sidv[_CHAN_k].status == ACCPT) && (s1->sidv[_CHAN_k].id == _CHAN_k_MID_start)) {
          char vw[MARKING_N_BYTES] = {0x40, 0x1c, 0x00, 0x00, 0x00};
          char t[MARKING_N_BYTES] = {0x00, 0x02, 0xa0, 0x00, 0x00};
          memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
          memcpy((char *)s2, (char *)s1, size_state()); 
          for (i = 0; i < MARKING_N_BYTES; i++) {
            s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
          }
          s2->env._VAR__ = s1->sidv[_CHAN_k].value;
          {
            uchar r[N_CLOCKS] = {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
            memcpy(reset_clock,r,N_CLOCKS);
          }
          set_active_clocks(s2);
          init_succ_matrix(s1_matrix,new_matrix);
          reset_matrix(new_matrix);
          forward_proj_matrix(new_matrix);
          intersect_invariant_matrix(s2,new_matrix);
          if (!canonicalize_matrix(new_matrix)) {
            invariant_violation();
          }
          else {
            extrapolate_matrix(new_matrix); 
#ifdef VDIM
            s2->marx = hstore_matrix(new_matrix); 
#else
            memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
            lab->type = RCV; lab->k = _CHAN_k;
            lab->i = _CHAN_k_MID_start; lab->v = s1->sidv[_CHAN_k].value;
            stopped[_CHAN_k] = 1;
            doit(s1,lab,s2);
          }
      }
    }
    if (marking & 0x02) { /* trigger 14 */
      if ((s1->sidv[_CHAN_k].status == ACCPT) && (s1->sidv[_CHAN_k].id == _CHAN_k_MID_pumpon)) {
          char vw[MARKING_N_BYTES] = {0x00, 0x02, 0x80, 0x00, 0x00};
          char t[MARKING_N_BYTES] = {0x00, 0x01, 0x00, 0x00, 0x00};
          memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
          memcpy((char *)s2, (char *)s1, size_state()); 
          for (i = 0; i < MARKING_N_BYTES; i++) {
            s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
          }
          s2->env._VAR__ = s1->sidv[_CHAN_k].value;
          {
            uchar r[N_CLOCKS] = {1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0};
            memcpy(reset_clock,r,N_CLOCKS);
          }
          set_active_clocks(s2);
          init_succ_matrix(s1_matrix,new_matrix);
          reset_matrix(new_matrix);
          forward_proj_matrix(new_matrix);
          intersect_invariant_matrix(s2,new_matrix);
          if (!canonicalize_matrix(new_matrix)) {
            invariant_violation();
          }
          else {
            extrapolate_matrix(new_matrix); 
#ifdef VDIM
            s2->marx = hstore_matrix(new_matrix); 
#else
            memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
            lab->type = RCV; lab->k = _CHAN_k;
            lab->i = _CHAN_k_MID_pumpon; lab->v = s1->sidv[_CHAN_k].value;
            stopped[_CHAN_k] = 1;
            doit(s1,lab,s2);
          }
      }
    }
    if (marking & 0x01) { /* trigger 15 */
        memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
        intersect_lower_bound_matrix(s1_matrix, 4, 200);
        if (canonicalize_matrix(s1_matrix)) {
          char vw[MARKING_N_BYTES] = {0x00, 0x01, 0x00, 0x00, 0x00};
          char t[MARKING_N_BYTES] = {0x00, 0x02, 0x80, 0x00, 0x00};
          memcpy((char *)s2, (char *)s1, size_state()); 
          for (i = 0; i < MARKING_N_BYTES; i++) {
            s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
          }
          {
            uchar r[N_CLOCKS] = {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
            memcpy(reset_clock,r,N_CLOCKS);
          }
          lab->type = COMP; strcpy(lab->name,"OP_PumpOn");
          OP_PumpOn(&(s1->env),data);
          while (data->top->nxtElem) {
            pop(data,&(s2->env));
            set_active_clocks(s2);
            init_succ_matrix(s1_matrix,new_matrix);
            reset_matrix(new_matrix);
            forward_proj_matrix(new_matrix);
            intersect_invariant_matrix(s2,new_matrix);
            if (!canonicalize_matrix(new_matrix)) {
              invariant_violation();
            }
            else {
              extrapolate_matrix(new_matrix); 
#ifdef VDIM
              s2->marx = hstore_matrix(new_matrix); 
#else
              memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
              doit(s1,lab,s2);
            }
          }
        }
    }
  }

  marking = s1->marking[2];
  if (marking != 0) {
    if (marking & 0x80) { /* trigger 16 */
      if ((s1->sidv[_CHAN_k].status == ACCPT) && (s1->sidv[_CHAN_k].id == _CHAN_k_MID_pumpoff)) {
          char vw[MARKING_N_BYTES] = {0x00, 0x02, 0x80, 0x00, 0x00};
          char t[MARKING_N_BYTES] = {0x00, 0x00, 0x40, 0x00, 0x00};
          memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
          memcpy((char *)s2, (char *)s1, size_state()); 
          for (i = 0; i < MARKING_N_BYTES; i++) {
            s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
          }
          s2->env._VAR__ = s1->sidv[_CHAN_k].value;
          {
            uchar r[N_CLOCKS] = {1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0};
            memcpy(reset_clock,r,N_CLOCKS);
          }
          set_active_clocks(s2);
          init_succ_matrix(s1_matrix,new_matrix);
          reset_matrix(new_matrix);
          forward_proj_matrix(new_matrix);
          intersect_invariant_matrix(s2,new_matrix);
          if (!canonicalize_matrix(new_matrix)) {
            invariant_violation();
          }
          else {
            extrapolate_matrix(new_matrix); 
#ifdef VDIM
            s2->marx = hstore_matrix(new_matrix); 
#else
            memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
            lab->type = RCV; lab->k = _CHAN_k;
            lab->i = _CHAN_k_MID_pumpoff; lab->v = s1->sidv[_CHAN_k].value;
            stopped[_CHAN_k] = 1;
            doit(s1,lab,s2);
          }
      }
    }
    if (marking & 0x40) { /* trigger 17 */
        memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
        intersect_lower_bound_matrix(s1_matrix, 4, 200);
        if (canonicalize_matrix(s1_matrix)) {
          char vw[MARKING_N_BYTES] = {0x00, 0x00, 0x40, 0x00, 0x00};
          char t[MARKING_N_BYTES] = {0x00, 0x02, 0x80, 0x00, 0x00};
          memcpy((char *)s2, (char *)s1, size_state()); 
          for (i = 0; i < MARKING_N_BYTES; i++) {
            s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
          }
          {
            uchar r[N_CLOCKS] = {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
            memcpy(reset_clock,r,N_CLOCKS);
          }
          lab->type = COMP; strcpy(lab->name,"OP_PumpOff");
          OP_PumpOff(&(s1->env),data);
          while (data->top->nxtElem) {
            pop(data,&(s2->env));
            set_active_clocks(s2);
            init_succ_matrix(s1_matrix,new_matrix);
            reset_matrix(new_matrix);
            forward_proj_matrix(new_matrix);
            intersect_invariant_matrix(s2,new_matrix);
            if (!canonicalize_matrix(new_matrix)) {
              invariant_violation();
            }
            else {
              extrapolate_matrix(new_matrix); 
#ifdef VDIM
              s2->marx = hstore_matrix(new_matrix); 
#else
              memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
              doit(s1,lab,s2);
            }
          }
        }
    }
    if (marking & 0x20) { /* trigger 18 */
      if ((s1->sidv[_CHAN_k].status == ACCPT) && (s1->sidv[_CHAN_k].id == _CHAN_k_MID_shutdown)) {
          char vw[MARKING_N_BYTES] = {0x00, 0x03, 0xe0, 0x00, 0x00};
          char t[MARKING_N_BYTES] = {0x00, 0x00, 0x10, 0x00, 0x00};
          memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
          memcpy((char *)s2, (char *)s1, size_state()); 
          for (i = 0; i < MARKING_N_BYTES; i++) {
            s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
          }
          s2->env._VAR__ = s1->sidv[_CHAN_k].value;
          {
            uchar r[N_CLOCKS] = {1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0};
            memcpy(reset_clock,r,N_CLOCKS);
          }
          set_active_clocks(s2);
          init_succ_matrix(s1_matrix,new_matrix);
          reset_matrix(new_matrix);
          forward_proj_matrix(new_matrix);
          intersect_invariant_matrix(s2,new_matrix);
          if (!canonicalize_matrix(new_matrix)) {
            invariant_violation();
          }
          else {
            extrapolate_matrix(new_matrix); 
#ifdef VDIM
            s2->marx = hstore_matrix(new_matrix); 
#else
            memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
            lab->type = RCV; lab->k = _CHAN_k;
            lab->i = _CHAN_k_MID_shutdown; lab->v = s1->sidv[_CHAN_k].value;
            stopped[_CHAN_k] = 1;
            doit(s1,lab,s2);
          }
      }
    }
    if (marking & 0x10) { /* trigger 19 */
        memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
        intersect_lower_bound_matrix(s1_matrix, 6, 200);
        if (canonicalize_matrix(s1_matrix)) {
          char vw[MARKING_N_BYTES] = {0x00, 0x00, 0x10, 0x00, 0x00};
          char t[MARKING_N_BYTES] = {0x40, 0x00, 0x00, 0x00, 0x00};
          memcpy((char *)s2, (char *)s1, size_state()); 
          for (i = 0; i < MARKING_N_BYTES; i++) {
            s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
          }
          {
            uchar r[N_CLOCKS] = {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
            memcpy(reset_clock,r,N_CLOCKS);
          }
          lab->type = COMP; strcpy(lab->name,"OP_PumpOff");
          OP_PumpOff(&(s1->env),data);
          while (data->top->nxtElem) {
            pop(data,&(s2->env));
            set_active_clocks(s2);
            init_succ_matrix(s1_matrix,new_matrix);
            reset_matrix(new_matrix);
            forward_proj_matrix(new_matrix);
            intersect_invariant_matrix(s2,new_matrix);
            if (!canonicalize_matrix(new_matrix)) {
              invariant_violation();
            }
            else {
              extrapolate_matrix(new_matrix); 
#ifdef VDIM
              s2->marx = hstore_matrix(new_matrix); 
#else
              memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
              doit(s1,lab,s2);
            }
          }
        }
    }
    if (marking & 0x08) { /* trigger 20 */
        memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
        intersect_lower_bound_matrix(s1_matrix, 5, 400);
        if (canonicalize_matrix(s1_matrix)) {
          char vw[MARKING_N_BYTES] = {0x00, 0x00, 0x08, 0x00, 0x00};
          char t[MARKING_N_BYTES] = {0x00, 0x00, 0x05, 0x00, 0x00};
          memcpy((char *)s2, (char *)s1, size_state()); 
          for (i = 0; i < MARKING_N_BYTES; i++) {
            s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
          }
          {
            uchar r[N_CLOCKS] = {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
            memcpy(reset_clock,r,N_CLOCKS);
          }
          lab->type = COMP; strcpy(lab->name,"OP_InitController");
          OP_InitController(&(s1->env),data);
          while (data->top->nxtElem) {
            pop(data,&(s2->env));
            set_active_clocks(s2);
            init_succ_matrix(s1_matrix,new_matrix);
            reset_matrix(new_matrix);
            forward_proj_matrix(new_matrix);
            intersect_invariant_matrix(s2,new_matrix);
            if (!canonicalize_matrix(new_matrix)) {
              invariant_violation();
            }
            else {
              extrapolate_matrix(new_matrix); 
#ifdef VDIM
              s2->marx = hstore_matrix(new_matrix); 
#else
              memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
              doit(s1,lab,s2);
            }
          }
        }
    }
    if (marking & 0x04) { /* trigger 21 */
      if ((s1->sidv[_CHAN_k].status == ACCPT) && (s1->sidv[_CHAN_k].id == _CHAN_k_MID_sensor_ready)) {
          char vw[MARKING_N_BYTES] = {0x00, 0x00, 0x05, 0x00, 0x00};
          char t[MARKING_N_BYTES] = {0x00, 0x00, 0x02, 0x00, 0x00};
          memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
          memcpy((char *)s2, (char *)s1, size_state()); 
          for (i = 0; i < MARKING_N_BYTES; i++) {
            s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
          }
          s2->env._VAR__ = s1->sidv[_CHAN_k].value;
          {
            uchar r[N_CLOCKS] = {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
            memcpy(reset_clock,r,N_CLOCKS);
          }
          set_active_clocks(s2);
          init_succ_matrix(s1_matrix,new_matrix);
          reset_matrix(new_matrix);
          forward_proj_matrix(new_matrix);
          intersect_invariant_matrix(s2,new_matrix);
          if (!canonicalize_matrix(new_matrix)) {
            invariant_violation();
          }
          else {
            extrapolate_matrix(new_matrix); 
#ifdef VDIM
            s2->marx = hstore_matrix(new_matrix); 
#else
            memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
            lab->type = RCV; lab->k = _CHAN_k;
            lab->i = _CHAN_k_MID_sensor_ready; lab->v = s1->sidv[_CHAN_k].value;
            stopped[_CHAN_k] = 1;
            doit(s1,lab,s2);
          }
      }
    }
    if (marking & 0x02) { /* trigger 22 */
      if ((s1->sidv[_CHAN_k].status == ACCPT) && (s1->sidv[_CHAN_k].id == _CHAN_k_MID_pump_ready)) {
          char vw[MARKING_N_BYTES] = {0x00, 0x00, 0x02, 0x00, 0x00};
          char t[MARKING_N_BYTES] = {0x00, 0x00, 0x00, 0x40, 0x00};
          memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
          memcpy((char *)s2, (char *)s1, size_state()); 
          for (i = 0; i < MARKING_N_BYTES; i++) {
            s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
          }
          s2->env._VAR__ = s1->sidv[_CHAN_k].value;
          {
            uchar r[N_CLOCKS] = {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
            memcpy(reset_clock,r,N_CLOCKS);
          }
          set_active_clocks(s2);
          init_succ_matrix(s1_matrix,new_matrix);
          reset_matrix(new_matrix);
          forward_proj_matrix(new_matrix);
          intersect_invariant_matrix(s2,new_matrix);
          if (!canonicalize_matrix(new_matrix)) {
            invariant_violation();
          }
          else {
            extrapolate_matrix(new_matrix); 
#ifdef VDIM
            s2->marx = hstore_matrix(new_matrix); 
#else
            memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
            lab->type = RCV; lab->k = _CHAN_k;
            lab->i = _CHAN_k_MID_pump_ready; lab->v = s1->sidv[_CHAN_k].value;
            stopped[_CHAN_k] = 1;
            doit(s1,lab,s2);
          }
      }
    }
    if (marking & 0x01) { /* trigger 23 */
      if ((s1->sidv[_CHAN_k].status == ACCPT) && (s1->sidv[_CHAN_k].id == _CHAN_k_MID_pump_ready)) {
          char vw[MARKING_N_BYTES] = {0x00, 0x00, 0x05, 0x00, 0x00};
          char t[MARKING_N_BYTES] = {0x00, 0x00, 0x00, 0x80, 0x00};
          memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
          memcpy((char *)s2, (char *)s1, size_state()); 
          for (i = 0; i < MARKING_N_BYTES; i++) {
            s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
          }
          s2->env._VAR__ = s1->sidv[_CHAN_k].value;
          {
            uchar r[N_CLOCKS] = {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
            memcpy(reset_clock,r,N_CLOCKS);
          }
          set_active_clocks(s2);
          init_succ_matrix(s1_matrix,new_matrix);
          reset_matrix(new_matrix);
          forward_proj_matrix(new_matrix);
          intersect_invariant_matrix(s2,new_matrix);
          if (!canonicalize_matrix(new_matrix)) {
            invariant_violation();
          }
          else {
            extrapolate_matrix(new_matrix); 
#ifdef VDIM
            s2->marx = hstore_matrix(new_matrix); 
#else
            memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
            lab->type = RCV; lab->k = _CHAN_k;
            lab->i = _CHAN_k_MID_pump_ready; lab->v = s1->sidv[_CHAN_k].value;
            stopped[_CHAN_k] = 1;
            doit(s1,lab,s2);
          }
      }
    }
  }

  marking = s1->marking[3];
  if (marking != 0) {
    if (marking & 0x80) { /* trigger 24 */
      if ((s1->sidv[_CHAN_k].status == ACCPT) && (s1->sidv[_CHAN_k].id == _CHAN_k_MID_sensor_ready)) {
          char vw[MARKING_N_BYTES] = {0x00, 0x00, 0x00, 0x80, 0x00};
          char t[MARKING_N_BYTES] = {0x00, 0x00, 0x00, 0x40, 0x00};
          memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
          memcpy((char *)s2, (char *)s1, size_state()); 
          for (i = 0; i < MARKING_N_BYTES; i++) {
            s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
          }
          s2->env._VAR__ = s1->sidv[_CHAN_k].value;
          {
            uchar r[N_CLOCKS] = {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
            memcpy(reset_clock,r,N_CLOCKS);
          }
          set_active_clocks(s2);
          init_succ_matrix(s1_matrix,new_matrix);
          reset_matrix(new_matrix);
          forward_proj_matrix(new_matrix);
          intersect_invariant_matrix(s2,new_matrix);
          if (!canonicalize_matrix(new_matrix)) {
            invariant_violation();
          }
          else {
            extrapolate_matrix(new_matrix); 
#ifdef VDIM
            s2->marx = hstore_matrix(new_matrix); 
#else
            memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
            lab->type = RCV; lab->k = _CHAN_k;
            lab->i = _CHAN_k_MID_sensor_ready; lab->v = s1->sidv[_CHAN_k].value;
            stopped[_CHAN_k] = 1;
            doit(s1,lab,s2);
          }
      }
    }
    if (marking & 0x40) { /* trigger 25 */
          char vw[MARKING_N_BYTES] = {0x00, 0x00, 0x00, 0x40, 0x00};
          char t[MARKING_N_BYTES] = {0x00, 0x00, 0x00, 0x20, 0x08};
          memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
          memcpy((char *)s2, (char *)s1, size_state()); 
          for (i = 0; i < MARKING_N_BYTES; i++) {
            s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
          }
          {
            uchar r[N_CLOCKS] = {1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0};
            memcpy(reset_clock,r,N_CLOCKS);
          }
          q_insert(s2,_CHAN_k,_CHAN_k_MID_start,s1->env._VAR__);
          set_active_clocks(s2);
          init_succ_matrix(s1_matrix,new_matrix);
          reset_matrix(new_matrix);
          forward_proj_matrix(new_matrix);
          intersect_invariant_matrix(s2,new_matrix);
          if (!canonicalize_matrix(new_matrix)) {
            invariant_violation();
          }
          else {
            extrapolate_matrix(new_matrix);
#ifdef VDIM
            s2->marx = hstore_matrix(new_matrix); 
#else
            memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
            lab->type = SND; lab->k = _CHAN_k;
            lab->i = _CHAN_k_MID_start; lab->v = s1->env._VAR__;
            doit(s1,lab,s2);
          }
    }
    if (marking & 0x20) { /* trigger 26 */
      if ((s1->sidv[_CHAN_k].status == ACCPT) && (s1->sidv[_CHAN_k].id == _CHAN_k_MID_level)) {
          char vw[MARKING_N_BYTES] = {0x00, 0x00, 0x00, 0x20, 0x08};
          char t[MARKING_N_BYTES] = {0x00, 0x00, 0x00, 0x10, 0x00};
          memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
          memcpy((char *)s2, (char *)s1, size_state()); 
          for (i = 0; i < MARKING_N_BYTES; i++) {
            s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
          }
          s2->env._VAR_w2 = s1->sidv[_CHAN_k].value;
          {
            uchar r[N_CLOCKS] = {1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0};
            memcpy(reset_clock,r,N_CLOCKS);
          }
          set_active_clocks(s2);
          init_succ_matrix(s1_matrix,new_matrix);
          reset_matrix(new_matrix);
          forward_proj_matrix(new_matrix);
          intersect_invariant_matrix(s2,new_matrix);
          if (!canonicalize_matrix(new_matrix)) {
            invariant_violation();
          }
          else {
            extrapolate_matrix(new_matrix); 
#ifdef VDIM
            s2->marx = hstore_matrix(new_matrix); 
#else
            memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
            lab->type = RCV; lab->k = _CHAN_k;
            lab->i = _CHAN_k_MID_level; lab->v = s1->sidv[_CHAN_k].value;
            stopped[_CHAN_k] = 1;
            doit(s1,lab,s2);
          }
      }
    }
    if (marking & 0x10) { /* trigger 27 */
        memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
        intersect_lower_bound_matrix(s1_matrix, 5, 10);
        if (canonicalize_matrix(s1_matrix)) {
          char vw[MARKING_N_BYTES] = {0x00, 0x00, 0x00, 0x10, 0x00};
          char t[MARKING_N_BYTES] = {0x00, 0x00, 0x00, 0x05, 0x00};
          memcpy((char *)s2, (char *)s1, size_state()); 
          for (i = 0; i < MARKING_N_BYTES; i++) {
            s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
          }
          {
            uchar r[N_CLOCKS] = {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
            memcpy(reset_clock,r,N_CLOCKS);
          }
          lab->type = COMP; strcpy(lab->name,"OP_TestHighLevel");
          OP_TestHighLevel(&(s1->env),data);
          while (data->top->nxtElem) {
            pop(data,&(s2->env));
            set_active_clocks(s2);
            init_succ_matrix(s1_matrix,new_matrix);
            reset_matrix(new_matrix);
            forward_proj_matrix(new_matrix);
            intersect_invariant_matrix(s2,new_matrix);
            if (!canonicalize_matrix(new_matrix)) {
              invariant_violation();
            }
            else {
              extrapolate_matrix(new_matrix); 
#ifdef VDIM
              s2->marx = hstore_matrix(new_matrix); 
#else
              memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
              doit(s1,lab,s2);
            }
          }
        }
    }
    if (marking & 0x08) { /* trigger 28 */
          char vw[MARKING_N_BYTES] = {0x00, 0x00, 0x00, 0x08, 0x00};
          char t[MARKING_N_BYTES] = {0x00, 0x00, 0x00, 0x20, 0x08};
          memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
          memcpy((char *)s2, (char *)s1, size_state()); 
          for (i = 0; i < MARKING_N_BYTES; i++) {
            s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
          }
          {
            uchar r[N_CLOCKS] = {1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0};
            memcpy(reset_clock,r,N_CLOCKS);
          }
          q_insert(s2,_CHAN_k,_CHAN_k_MID_pumpoff,s1->env._VAR__);
          set_active_clocks(s2);
          init_succ_matrix(s1_matrix,new_matrix);
          reset_matrix(new_matrix);
          forward_proj_matrix(new_matrix);
          intersect_invariant_matrix(s2,new_matrix);
          if (!canonicalize_matrix(new_matrix)) {
            invariant_violation();
          }
          else {
            extrapolate_matrix(new_matrix);
#ifdef VDIM
            s2->marx = hstore_matrix(new_matrix); 
#else
            memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
            lab->type = SND; lab->k = _CHAN_k;
            lab->i = _CHAN_k_MID_pumpoff; lab->v = s1->env._VAR__;
            doit(s1,lab,s2);
          }
    }
    if (marking & 0x04) { /* trigger 29 */
      if (PRED[29](&(s1->env))) { /* PRED_HighLevel */
          char vw[MARKING_N_BYTES] = {0x00, 0x00, 0x00, 0x05, 0x00};
          char t[MARKING_N_BYTES] = {0x00, 0x00, 0x00, 0x08, 0x00};
          memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
          memcpy((char *)s2, (char *)s1, size_state()); 
          for (i = 0; i < MARKING_N_BYTES; i++) {
            s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
          }
          {
            uchar r[N_CLOCKS] = {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
            memcpy(reset_clock,r,N_CLOCKS);
          }
          set_active_clocks(s2);
          init_succ_matrix(s1_matrix,new_matrix);
          reset_matrix(new_matrix);
          forward_proj_matrix(new_matrix);
          intersect_invariant_matrix(s2,new_matrix);
          if (!canonicalize_matrix(new_matrix)) {
            invariant_violation();
          }
          else {
            extrapolate_matrix(new_matrix); 
#ifdef VDIM
            s2->marx = hstore_matrix(new_matrix); 
#else
            memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
            lab->type = GU; strcpy(lab->name,"PRED_HighLevel");
            doit(s1,lab,s2);
          } 
        }
    }
    if (marking & 0x02) { /* trigger 30 */
        memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
        intersect_lower_bound_matrix(s1_matrix, 5, 10);
        if (canonicalize_matrix(s1_matrix)) {
          char vw[MARKING_N_BYTES] = {0x00, 0x00, 0x00, 0x02, 0x00};
          char t[MARKING_N_BYTES] = {0x00, 0x00, 0x00, 0x00, 0x50};
          memcpy((char *)s2, (char *)s1, size_state()); 
          for (i = 0; i < MARKING_N_BYTES; i++) {
            s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
          }
          {
            uchar r[N_CLOCKS] = {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
            memcpy(reset_clock,r,N_CLOCKS);
          }
          lab->type = COMP; strcpy(lab->name,"OP_TestLowLevel");
          OP_TestLowLevel(&(s1->env),data);
          while (data->top->nxtElem) {
            pop(data,&(s2->env));
            set_active_clocks(s2);
            init_succ_matrix(s1_matrix,new_matrix);
            reset_matrix(new_matrix);
            forward_proj_matrix(new_matrix);
            intersect_invariant_matrix(s2,new_matrix);
            if (!canonicalize_matrix(new_matrix)) {
              invariant_violation();
            }
            else {
              extrapolate_matrix(new_matrix); 
#ifdef VDIM
              s2->marx = hstore_matrix(new_matrix); 
#else
              memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
              doit(s1,lab,s2);
            }
          }
        }
    }
    if (marking & 0x01) { /* trigger 31 */
      if (PRED[31](&(s1->env))) { /* PRED_notHighLevel */
          char vw[MARKING_N_BYTES] = {0x00, 0x00, 0x00, 0x05, 0x00};
          char t[MARKING_N_BYTES] = {0x00, 0x00, 0x00, 0x02, 0x00};
          memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
          memcpy((char *)s2, (char *)s1, size_state()); 
          for (i = 0; i < MARKING_N_BYTES; i++) {
            s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
          }
          {
            uchar r[N_CLOCKS] = {1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0};
            memcpy(reset_clock,r,N_CLOCKS);
          }
          set_active_clocks(s2);
          init_succ_matrix(s1_matrix,new_matrix);
          reset_matrix(new_matrix);
          forward_proj_matrix(new_matrix);
          intersect_invariant_matrix(s2,new_matrix);
          if (!canonicalize_matrix(new_matrix)) {
            invariant_violation();
          }
          else {
            extrapolate_matrix(new_matrix); 
#ifdef VDIM
            s2->marx = hstore_matrix(new_matrix); 
#else
            memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
            lab->type = GU; strcpy(lab->name,"PRED_notHighLevel");
            doit(s1,lab,s2);
          } 
        }
    }
  }

  marking = s1->marking[4];
  if (marking != 0) {
    if (marking & 0x80) { /* trigger 32 */
          char vw[MARKING_N_BYTES] = {0x00, 0x00, 0x00, 0x00, 0x80};
          char t[MARKING_N_BYTES] = {0x00, 0x00, 0x00, 0x20, 0x08};
          memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
          memcpy((char *)s2, (char *)s1, size_state()); 
          for (i = 0; i < MARKING_N_BYTES; i++) {
            s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
          }
          {
            uchar r[N_CLOCKS] = {1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0};
            memcpy(reset_clock,r,N_CLOCKS);
          }
          q_insert(s2,_CHAN_k,_CHAN_k_MID_pumpon,s1->env._VAR__);
          set_active_clocks(s2);
          init_succ_matrix(s1_matrix,new_matrix);
          reset_matrix(new_matrix);
          forward_proj_matrix(new_matrix);
          intersect_invariant_matrix(s2,new_matrix);
          if (!canonicalize_matrix(new_matrix)) {
            invariant_violation();
          }
          else {
            extrapolate_matrix(new_matrix);
#ifdef VDIM
            s2->marx = hstore_matrix(new_matrix); 
#else
            memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
            lab->type = SND; lab->k = _CHAN_k;
            lab->i = _CHAN_k_MID_pumpon; lab->v = s1->env._VAR__;
            doit(s1,lab,s2);
          }
    }
    if (marking & 0x40) { /* trigger 33 */
      if (PRED[33](&(s1->env))) { /* PRED_LowLevel */
          char vw[MARKING_N_BYTES] = {0x00, 0x00, 0x00, 0x00, 0x50};
          char t[MARKING_N_BYTES] = {0x00, 0x00, 0x00, 0x00, 0x80};
          memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
          memcpy((char *)s2, (char *)s1, size_state()); 
          for (i = 0; i < MARKING_N_BYTES; i++) {
            s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
          }
          {
            uchar r[N_CLOCKS] = {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
            memcpy(reset_clock,r,N_CLOCKS);
          }
          set_active_clocks(s2);
          init_succ_matrix(s1_matrix,new_matrix);
          reset_matrix(new_matrix);
          forward_proj_matrix(new_matrix);
          intersect_invariant_matrix(s2,new_matrix);
          if (!canonicalize_matrix(new_matrix)) {
            invariant_violation();
          }
          else {
            extrapolate_matrix(new_matrix); 
#ifdef VDIM
            s2->marx = hstore_matrix(new_matrix); 
#else
            memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
            lab->type = GU; strcpy(lab->name,"PRED_LowLevel");
            doit(s1,lab,s2);
          } 
        }
    }
    if (marking & 0x20) { /* trigger 34 */
        memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
        intersect_lower_bound_matrix(s1_matrix, 1, 0);
        if (canonicalize_matrix(s1_matrix)) {
          char vw[MARKING_N_BYTES] = {0x00, 0x00, 0x00, 0x00, 0x20};
          char t[MARKING_N_BYTES] = {0x00, 0x00, 0x00, 0x20, 0x08};
          memcpy((char *)s2, (char *)s1, size_state()); 
          for (i = 0; i < MARKING_N_BYTES; i++) {
            s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
          }
          {
            uchar r[N_CLOCKS] = {1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0};
            memcpy(reset_clock,r,N_CLOCKS);
          }
          lab->type = COMP; strcpy(lab->name,"OP_ID");
          OP_ID(&(s1->env),data);
          while (data->top->nxtElem) {
            pop(data,&(s2->env));
            set_active_clocks(s2);
            init_succ_matrix(s1_matrix,new_matrix);
            reset_matrix(new_matrix);
            forward_proj_matrix(new_matrix);
            intersect_invariant_matrix(s2,new_matrix);
            if (!canonicalize_matrix(new_matrix)) {
              invariant_violation();
            }
            else {
              extrapolate_matrix(new_matrix); 
#ifdef VDIM
              s2->marx = hstore_matrix(new_matrix); 
#else
              memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
              doit(s1,lab,s2);
            }
          }
        }
    }
    if (marking & 0x10) { /* trigger 35 */
      if (PRED[35](&(s1->env))) { /* PRED_notLowLevel */
          char vw[MARKING_N_BYTES] = {0x00, 0x00, 0x00, 0x00, 0x50};
          char t[MARKING_N_BYTES] = {0x00, 0x00, 0x00, 0x00, 0x20};
          memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
          memcpy((char *)s2, (char *)s1, size_state()); 
          for (i = 0; i < MARKING_N_BYTES; i++) {
            s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
          }
          {
            uchar r[N_CLOCKS] = {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
            memcpy(reset_clock,r,N_CLOCKS);
          }
          set_active_clocks(s2);
          init_succ_matrix(s1_matrix,new_matrix);
          reset_matrix(new_matrix);
          forward_proj_matrix(new_matrix);
          intersect_invariant_matrix(s2,new_matrix);
          if (!canonicalize_matrix(new_matrix)) {
            invariant_violation();
          }
          else {
            extrapolate_matrix(new_matrix); 
#ifdef VDIM
            s2->marx = hstore_matrix(new_matrix); 
#else
            memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
            lab->type = GU; strcpy(lab->name,"PRED_notLowLevel");
            doit(s1,lab,s2);
          } 
        }
    }
    if (marking & 0x08) { /* trigger 36 */
        memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
        intersect_lower_bound_matrix(s1_matrix, 5, 15000);
        if (canonicalize_matrix(s1_matrix)) {
          char vw[MARKING_N_BYTES] = {0x00, 0x00, 0x00, 0x20, 0x08};
          char t[MARKING_N_BYTES] = {0x00, 0x00, 0x00, 0x00, 0x04};
          memcpy((char *)s2, (char *)s1, size_state()); 
          for (i = 0; i < MARKING_N_BYTES; i++) {
            s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
          }
          {
            uchar r[N_CLOCKS] = {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
            memcpy(reset_clock,r,N_CLOCKS);
          }
          lab->type = COMP; strcpy(lab->name,"OP_SensorTimedOut");
          OP_SensorTimedOut(&(s1->env),data);
          while (data->top->nxtElem) {
            pop(data,&(s2->env));
            set_active_clocks(s2);
            init_succ_matrix(s1_matrix,new_matrix);
            reset_matrix(new_matrix);
            forward_proj_matrix(new_matrix);
            intersect_invariant_matrix(s2,new_matrix);
            if (!canonicalize_matrix(new_matrix)) {
              invariant_violation();
            }
            else {
              extrapolate_matrix(new_matrix); 
#ifdef VDIM
              s2->marx = hstore_matrix(new_matrix); 
#else
              memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
              doit(s1,lab,s2);
            }
          }
        }
    }
    if (marking & 0x04) { /* trigger 37 */
          char vw[MARKING_N_BYTES] = {0x00, 0x00, 0x00, 0x00, 0x04};
          char t[MARKING_N_BYTES] = {0x40, 0x00, 0x00, 0x00, 0x00};
          memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
          memcpy((char *)s2, (char *)s1, size_state()); 
          for (i = 0; i < MARKING_N_BYTES; i++) {
            s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
          }
          {
            uchar r[N_CLOCKS] = {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
            memcpy(reset_clock,r,N_CLOCKS);
          }
          q_insert(s2,_CHAN_k,_CHAN_k_MID_shutdown,s1->env._VAR__);
          set_active_clocks(s2);
          init_succ_matrix(s1_matrix,new_matrix);
          reset_matrix(new_matrix);
          forward_proj_matrix(new_matrix);
          intersect_invariant_matrix(s2,new_matrix);
          if (!canonicalize_matrix(new_matrix)) {
            invariant_violation();
          }
          else {
            extrapolate_matrix(new_matrix);
#ifdef VDIM
            s2->marx = hstore_matrix(new_matrix); 
#else
            memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
            lab->type = SND; lab->k = _CHAN_k;
            lab->i = _CHAN_k_MID_shutdown; lab->v = s1->env._VAR__;
            doit(s1,lab,s2);
          }
    }
  }

  /* network transitions */
  for (k = 0; k < N_CHANNELS; k++) {
    switch (s1->sidv[k].status) {
    case FREE :
      memcpy((char *)s2, (char *)s1, size_state()); 
      if (q_trans(s2,k)) {
        memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
        memset(reset_clock,0,N_CLOCKS);
        reset_clock[0] = 1; reset_clock[1] = 1;
        reset_clock[net_clocks[k]] = 1;    
        set_active_clocks(s2);
        init_succ_matrix(s1_matrix,new_matrix);
        reset_matrix(new_matrix);
        forward_proj_matrix(new_matrix);
        intersect_invariant_matrix(s2,new_matrix);
        if (!canonicalize_matrix(new_matrix)) {
          invariant_violation();
        }
        else {
          extrapolate_matrix(new_matrix); 
#ifdef VDIM
          s2->marx = hstore_matrix(new_matrix); 
#else
          memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
          lab->type = FP; 
          lab->k = k; lab->i = s2->sidv[k].id; lab->v = s2->sidv[k].value;
          doit(s1,lab,s2);
        }
      }
      break;
    case PRE :
      memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
      intersect_lower_bound_matrix(s1_matrix,net_clocks[k],dlb(k,s1->sidv[k].id));
      if (canonicalize_matrix(s1_matrix)) {
        memcpy((char *)s2, (char *)s1, size_state()); 
        s2->sidv[k].status = ACCPT;
        memset(reset_clock,0,N_CLOCKS);
        reset_clock[0] = 1; reset_clock[1] = 1;
        set_active_clocks(s2);
        init_succ_matrix(s1_matrix,new_matrix);
        reset_matrix(new_matrix);
        forward_proj_matrix(new_matrix);
        intersect_invariant_matrix(s2,new_matrix);
        if (!canonicalize_matrix(new_matrix)) {
          invariant_violation();
        }
        else {
          extrapolate_matrix(new_matrix); 
#ifdef VDIM
          s2->marx = hstore_matrix(new_matrix); 
#else
          memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
          lab->type = PA; 
          lab->k = k; lab->i = s2->sidv[k].id; lab->v = s2->sidv[k].value;
          doit(s1,lab,s2);
        }
      }
      break;
    case ACCPT : 
      if (!stopped[k]) {
        memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
        memcpy((char *)s2, (char *)s1, size_state()); 
        s2->sidv[k].status = POST;
        memset(reset_clock,0,N_CLOCKS);
        reset_clock[0] = 1; reset_clock[1] = 1;
        reset_clock[net_clocks[k]] = 1;    
        set_active_clocks(s2);
        init_succ_matrix(s1_matrix,new_matrix);
        reset_matrix(new_matrix);
        forward_proj_matrix(new_matrix);
        intersect_invariant_matrix(s2,new_matrix);
        if (!canonicalize_matrix(new_matrix)) {
          invariant_violation();
        }
        else {
          extrapolate_matrix(new_matrix); 
#ifdef VDIM
          s2->marx = hstore_matrix(new_matrix); 
#else
          memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
          lab->type = AP; 
          lab->k = k; 
          doit(s1,lab,s2);
        }
      }
      break;
    case POST : 
      memcpy(s1_matrix,s1->marx,size_matrix(s1->marx));
      intersect_lower_bound_matrix(s1_matrix,net_clocks[k],dlB(k,s1->sidv[k].id));
      if (canonicalize_matrix(s1_matrix)) {
        memcpy((char *)s2, (char *)s1, size_state()); 
        s2->sidv[k].status = FREE;
        s2->sidv[k].id = 0;
        s2->sidv[k].value = 0;
        memset(reset_clock,0,N_CLOCKS);
        reset_clock[0] = 1; reset_clock[1] = 1;
        set_active_clocks(s2);
        init_succ_matrix(s1_matrix,new_matrix);
        reset_matrix(new_matrix);
        forward_proj_matrix(new_matrix);
        intersect_invariant_matrix(s2,new_matrix);
        if (!canonicalize_matrix(new_matrix)) {
          invariant_violation();
        }
        else {
          extrapolate_matrix(new_matrix); 
#ifdef VDIM
          s2->marx = hstore_matrix(new_matrix); 
#else
          memcpy(s2->marx, new_matrix, MATRIX_N_BYTES);
#endif 
          lab->type = PF; 
          lab->k = k; 
          doit(s1,lab,s2);
        }
      }
      break;    
    }
  }
}


void 
transition(state_vector_t *s1, label_t *lab, state_vector_t *s2) {
#ifdef SIM
  memcpy(global_state_array + global_transition_number,s2,size_state());
  printf("%3d) ",global_transition_number);
  print_label(lab); printf("\n");
  global_transition_number += 1;
#else
#ifdef MA
  if (!dfa_store((uchar *)s2)) {
#else
  if (!hstore(state_table,(char *)s2,size_state())) {
#endif
#ifdef BFS
    enqueue(to_do,s2);
#else
    push(to_do,s2);
#endif
#ifdef VVERBOSE
    printf("state %6d : ",global_state_number);
    print_state_vector_bytes(s2);
    printf("\n");
#endif
    global_state_number += 1;
#ifdef VERBOSE
    if ((global_state_number % 100) == 0) {
      printf("#states : %8d\n",global_state_number);
    }
#endif
  }  
  global_transition_number += 1;
#endif
}


int 
main () {
  label_t label;
  state_vector_t *current_state = (state_vector_t *)emalloc(sizeof(state_vector_t));
  state_vector_t *new_state = (state_vector_t *)emalloc(sizeof(state_vector_t));
#ifdef SIM
  int option;
  data = new_stack(sizeof(data_env_t));
  start_state((state_vector_t *)current_state);
  while (1) {
    print_state(current_state); printf("\n\n");
    iterate_state(current_state,&label,new_state,transition);
    do {
      printf("\n\nNext : "); fflush(stdout);
      scanf("%d",&option);
    } while ((option < 0) || (option >= global_transition_number));
    global_transition_number = 0;
    memcpy(current_state,global_state_array+option,size_state());
  }
#else
  data = new_stack(sizeof(data_env_t));
#ifdef BFS
  to_do = new_queue(sizeof(state_vector_t));
#else
  to_do = new_stack(sizeof(state_vector_t));
#endif
#ifdef MA
  dfa_init(size_state());
#else
  hinit(state_table,SSIZE);
#endif
#ifdef VDIM
  hinit(marx_table,MSIZE);
#endif
  start_state((state_vector_t *)current_state);
#ifdef VVERBOSE
  printf("state %6d : ",global_state_number);
  print_state_vector_bytes((state_vector_t *)current_state);
  printf("\n");
#endif
#ifdef MA
  dfa_store((uchar *)current_state);
#else
  hstore(state_table,(char *)current_state,size_state());
#endif
#ifdef BFS
  enqueue(to_do,current_state);
#else
  push(to_do,current_state);
#endif
  global_state_number+=1;
#ifdef BFS
  while (is_non_empty_q(to_do)) {
    dequeue(to_do,current_state);
#else
  while (is_non_empty_stk(to_do)) {
    pop(to_do,current_state);
#endif
    iterate_state(current_state,&label,new_state,transition);
  }
#ifdef VERBOSE
  printf("#state vector bytes   %8d\n", size_state());
  print_state_vector_boundaries((state_vector_t *)current_state);
#ifndef MA
  printf("state hash conflicts (resolved) %g\n",state_table->hcmp);
#endif
#ifdef VDIM
  printf("matrix hash conflicts (resolved) %g\n",marx_table->hcmp);
#endif
#endif
  if (global_invariant_violations) {
    printf("ERROR: %d invariant violations\n", global_invariant_violations);
  }
  printf("#states               %8d\n", global_state_number);
  printf("#trans                %8d\n", global_transition_number);
#ifdef VDIM
  printf("#matrices             %8d\n", global_matrix_number);
#endif
#ifdef MA
  dfa_stats();
#endif
#ifdef MEMCNT
  printf("%-6.3f memory usage (Mbyte)\n\n",memcnt/1000000.);
#endif
  exit(0);
#endif 
}
