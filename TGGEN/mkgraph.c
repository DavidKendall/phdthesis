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
  exit(0);
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

#define BLANK_MESSAGE 0xffffffff

#define N_PLACES 6

#define MARKING_N_BYTES 1

#define N_CHANNELS 1

#define MAX_N_MIDS 1

#define QSZ 1

#define N_CLOCKS 5

#define LABEL_NAME_MAX_N_CHARS 1024

typedef enum {FREE=0, PRE=1, ACCPT=2, POST=3} status_t;

typedef enum {SND=0, RCV=1, COMP=2, GU=3, FP=4, PA=5, AP=6, PF=7} label_type_t;

typedef enum {_CHAN_k=0} chan_id_t;

typedef enum {_CHAN_k_MID_pressure=0} _CHAN_k_MID_t;

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

#include "./valve_data.c"

typedef struct {
  uchar        marking[MARKING_N_BYTES];
  data_env_t   env;
  sidv_t       sidv[N_CHANNELS];
  message_t    q[QSZ];
} state_vector_t;

typedef struct {
  state_vector_t vector;
  int            number;
} state_t;

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
  uint        bound;
} upper_bound_t;

typedef void (*state_operator_t)(state_vector_t *, label_t *, state_vector_t *);

#define pri(k,i) (net_static[k][i]._pri)
#define dlb(k,i) (net_static[k][i]._dlb)
#define dub(k,i) (net_static[k][i]._dub)
#define dlB(k,i) (net_static[k][i]._dlB)
#define duB(k,i) (net_static[k][i]._duB)

static net_static_t net_static =
{{{1, 43, 53, 10, 12}}};

static short n_mids_per_chan[N_CHANNELS] = {1};

static short q_max_n[N_CHANNELS] = {1};

static short q_offset[N_CHANNELS] = {0};

static short net_clocks[N_CHANNELS] = {2};

static upper_bound_t tinv[N_PLACES] =
  {{-1,0}, {-1,0}, {4,10}, {1,0}, {-1,0}, {3,30}
  };

static queue_t *q;
static stack_t *data;
Hash_table_t loc_table_data;
Hash_table_t *loc_table = &loc_table_data;
static int global_state_number = 0;
static int global_transition_number = 0;
#ifdef TG
FILE *graph_output;
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
  fprintf(f, "State vector boundaries: marking  %ld, env %ld, sidv %ld, q %ld\n",
    ((ulong)&(svec->marking) - (ulong)svec), 
    ((ulong)&(svec->env) - (ulong)svec), 
    ((ulong)&(svec->sidv) - (ulong)svec),
    ((ulong)&(svec->q) - (ulong)svec));
}

void
print_state_vector_boundaries(state_vector_t *svec) {
  fprint_state_vector_boundaries(stdout,svec);
}

void
fprint_label(FILE *f, label_t *lab) {
  int i;

  if (lab->clock >= 0) {
    fprintf(f,"C%d >= %d => ",lab->clock,lab->bound);
  }
  else {
    fprintf(f,"true => ");
  }
  switch (lab->type) {
  case SND:
    fprintf(f,"SND_%d_%d_%d; reset{",lab->k,lab->i,lab->v);
    break;
  case RCV:
    fprintf(f,"RCV_%d_%d_%d; reset{",lab->k,lab->i,lab->v);
    break;
  case COMP:
    fprintf(f,"%s; reset {", lab->name);
    break;
  case GU:
    fprintf(f,"%s; reset {", lab->name);
    break;
  case FP:
    fprintf(f,"FP_%d_%d_%d; reset{",lab->k,lab->i,lab->v);
    break;
  case PA:
    fprintf(f,"PA_%d_%d_%d; reset{",lab->k,lab->i,lab->v);
    break;
  case AP:
    fprintf(f,"AP_%d; reset{",lab->k);
    break;
  case PF:
    fprintf(f,"PF_%d; reset{",lab->k);
    break;
  default:
    uerror("unexpected label type");
    break;
  }
  if (lab->resets[0] != -1) {
    fprintf(f,"C%d",lab->resets[0]);
    for (i = 1; lab->resets[i] != -1; i++) {
      fprintf(f," C%d",lab->resets[i]);
    }
  }
  fprintf(f,"}; ");
}

void 
print_label(label_t *lab) {
  fprint_label(stdout,lab);
}

void 
fprint_clock_names (FILE *f) {
  int i;
  fprintf(f,"C0");
  for (i = 1; i < N_CLOCKS; i++) {
    fprintf(f," C%d",i);
  }
}

void
print_clock_names () {
  fprint_clock_names stdout;
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


#define size_state() (sizeof(state_vector_t))

void
start_state(state_vector_t *svec) {
  uchar init_marking[MARKING_N_BYTES] = {0x28};
  memcpy(&(svec->marking),&init_marking,MARKING_N_BYTES);
  memset(&(svec->q), 0xff, QSZ * sizeof(message_t)); 
}

void 
iterate_state(state_vector_t *s1, label_t *lab, 
              state_vector_t *s2, state_operator_t doit) {

  int i;
  uint k;
  uchar marking;
  int open_guard = 0;
  int stopped[N_CHANNELS] = {0};    

  marking = s1->marking[0];
  if (marking != 0) {
    if (marking & 0x80) {
      uerror("tick shouldn't happen");
    }
    if (marking & 0x40) {
      /* idle doesn't generate any transitions */
    }
    if (marking & 0x20) { /* trigger 2 */
        char vw[MARKING_N_BYTES] = {0x20};
        char t[MARKING_N_BYTES] = {0x10};
        memcpy((char *)s2, (char *)s1, size_state()); 
        for (i = 0; i < MARKING_N_BYTES; i++) {
          s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
        }
        lab->type = COMP; strcpy(lab->name,"OP_ReadSensor");
        lab->clock = 4; lab->bound = 5;
        lab->resets[0] = 1;
        lab->resets[1] = -1;
        OP_ReadSensor(&(s1->env),data);
        while (data->top->nxtElem) {
          pop(data,&(s2->env));
          doit(s1,lab,s2);
        }
    }
    if (marking & 0x10) { /* trigger 3 */
        char vw[MARKING_N_BYTES] = {0x10};
        char t[MARKING_N_BYTES] = {0x40};
        memcpy((char *)s2, (char *)s1, size_state()); 
        for (i = 0; i < MARKING_N_BYTES; i++) {
          s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
        }
        q_insert(s2,_CHAN_k,_CHAN_k_MID_pressure,s1->env._VAR_x);
        lab->type = SND; lab->k = _CHAN_k;
        lab->i = _CHAN_k_MID_pressure; lab->v = s1->env._VAR_x;
        lab->clock = -1; lab->bound = 0;
        if (s1->sidv[_CHAN_k].status == FREE) {
        lab->resets[0] = net_clocks[_CHAN_k];
        lab->resets[1] = -1;
        }
        else {
        lab->resets[0] = -1;
        }
        doit(s1,lab,s2);
    }
    if (marking & 0x08) { /* trigger 4 */
      if ((s1->sidv[_CHAN_k].status == ACCPT) && (s1->sidv[_CHAN_k].id == _CHAN_k_MID_pressure)) {
        char vw[MARKING_N_BYTES] = {0x08};
        char t[MARKING_N_BYTES] = {0x04};
        memcpy((char *)s2, (char *)s1, size_state()); 
        for (i = 0; i < MARKING_N_BYTES; i++) {
          s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
        }
        s2->env._VAR_y = s1->sidv[_CHAN_k].value;
        lab->type = RCV; lab->k = _CHAN_k;
        lab->i = _CHAN_k_MID_pressure; lab->v = s1->sidv[_CHAN_k].value;
        lab->clock = -1; lab->bound = 0;
        lab->resets[0] = 3;
        lab->resets[1] = -1;
        stopped[_CHAN_k] = 1;
        doit(s1,lab,s2);
      }
    }
    if (marking & 0x04) { /* trigger 5 */
        char vw[MARKING_N_BYTES] = {0x04};
        char t[MARKING_N_BYTES] = {0x40};
        memcpy((char *)s2, (char *)s1, size_state()); 
        for (i = 0; i < MARKING_N_BYTES; i++) {
          s2->marking[i] = (s1->marking[i] & ~vw[i]) | t[i];
        }
        lab->type = COMP; strcpy(lab->name,"OP_AdjustValve");
        lab->clock = 3; lab->bound = 20;
        lab->resets[0] = -1;
        OP_AdjustValve(&(s1->env),data);
        while (data->top->nxtElem) {
          pop(data,&(s2->env));
          doit(s1,lab,s2);
        }
    }
  }

  if (!open_guard) {/* network transitions */
    for (k = 0; k < N_CHANNELS; k++) {
      memcpy((char *)s2, (char *)s1, size_state()); 
      switch (s1->sidv[k].status) {
      case FREE :
        if (q_trans(s2,k)) {
          lab->type = FP; 
          lab->k = k; lab->i = s2->sidv[k].id; lab->v = s2->sidv[k].value;
          lab->clock = net_clocks[k]; lab->bound = 0;
          lab->resets[0] = net_clocks[k]; lab->resets[1] = -1;
          doit(s1,lab,s2);
        }
        break;
      case PRE : 
        s2->sidv[k].status = ACCPT;
        lab->type = PA; 
        lab->k = k; lab->i = s2->sidv[k].id; lab->v = s2->sidv[k].value;
        lab->clock = net_clocks[k]; lab->bound = dlb(k,s2->sidv[k].id);
        lab->resets[0] = net_clocks[k]; lab->resets[1] = -1;
        doit(s1,lab,s2);
        break;
      case ACCPT : 
        if (!stopped[k]) {
          s2->sidv[k].status = POST;
          lab->type = AP; 
          lab->k = k; 
          lab->clock = net_clocks[k]; lab->bound = 0; 
          lab->resets[0] = net_clocks[k]; lab->resets[1] = -1;
          doit(s1,lab,s2);
        }
        break;
      case POST : 
        s2->sidv[k].status = FREE;
        lab->type = PF; 
        lab->k = k; 
        lab->clock = net_clocks[k]; lab->bound = dlB(k,s2->sidv[k].id);
        lab->resets[0] = net_clocks[k]; lab->resets[1] = -1;
        doit(s1,lab,s2);
        break;
      }    
    }
  }
}


void
fprint_invariant(FILE *f, state_vector_t *svec) {
  int i,k;
  int first_conjunct = 1;

  for (k = 0; k < N_CHANNELS; k++) {
    switch (svec->sidv[k].status) {
    case FREE : {
      message_t *q = svec->q + q_offset[k];
      if ((*(uint *)q) != BLANK_MESSAGE) {
        if (first_conjunct) {
          first_conjunct = 0;
        }
        else {
          fprintf(f," AND ");
        }
        fprintf(f,"C%d <= 0", net_clocks[k]);
      }
      break;
    }
    case PRE :
      if (first_conjunct) {
        first_conjunct = 0;
      }
      else {
        fprintf(f," AND ");
      }
      fprintf(f,"C%d <= %d",net_clocks[k],dub(k,svec->sidv[k].id));
      break;
    case ACCPT :
      if (first_conjunct) {
        first_conjunct = 0;
      }
      else {
        fprintf(f," AND ");
      }
      fprintf(f,"C%d <= 0",net_clocks[k]);
      break;
    case POST :
      if (first_conjunct) {
        first_conjunct = 0;
      }
      else {
        fprintf(f," AND ");
      }
      fprintf(f,"C%d <= %d",net_clocks[k],duB(k,svec->sidv[k].id));
      break;
    }
  }

  for (i = 0; i < MARKING_N_BYTES; i++) {
    if (svec->marking[i]) {
      if ((svec->marking[i] & 0x80) && (tinv[i*8].clock > -1)) {
        if (first_conjunct) {
          first_conjunct = 0;
        }
        else {
          fprintf(f," AND ");
        }
        fprintf(f,"C%d <= %d",tinv[i*8].clock,tinv[i*8].bound);
      }
      if ((svec->marking[i] & 0x40) && (tinv[i*8+1].clock > -1)) {
        if (first_conjunct) {
          first_conjunct = 0;
        }
        else {
          fprintf(f," AND ");
        }
        fprintf(f,"C%d <= %d",tinv[i*8+1].clock,tinv[i*8+1].bound);
      }
      if ((svec->marking[i] & 0x20) && (tinv[i*8+2].clock > -1)) {
        if (first_conjunct) {
          first_conjunct = 0;
        }
        else {
          fprintf(f," AND ");
        }
        fprintf(f,"C%d <= %d",tinv[i*8+2].clock,tinv[i*8+2].bound);
      }
      if ((svec->marking[i] & 0x10) && (tinv[i*8+3].clock > -1)) {
        if (first_conjunct) {
          first_conjunct = 0;
        }
        else {
          fprintf(f," AND ");
        }
        fprintf(f,"C%d <= %d",tinv[i*8+3].clock,tinv[i*8+3].bound);
      }
      if ((svec->marking[i] & 0x08) && (tinv[i*8+4].clock > -1)) {
        if (first_conjunct) {
          first_conjunct = 0;
        }
        else {
          fprintf(f," AND ");
        }
        fprintf(f,"C%d <= %d",tinv[i*8+4].clock,tinv[i*8+4].bound);
      }
      if ((svec->marking[i] & 0x04) && (tinv[i*8+5].clock > -1)) {
        if (first_conjunct) {
          first_conjunct = 0;
        }
        else {
          fprintf(f," AND ");
        }
        fprintf(f,"C%d <= %d",tinv[i*8+5].clock,tinv[i*8+5].bound);
      }
      if ((svec->marking[i] & 0x02) && (tinv[i*8+6].clock > -1)) {
        if (first_conjunct) {
          first_conjunct = 0;
        }
        else {
          fprintf(f," AND ");
        }
        fprintf(f,"C%d <= %d",tinv[i*8+6].clock,tinv[i*8+6].bound);
      }
      if ((svec->marking[i] & 0x01) && (tinv[i*8+7].clock > -1)) {
        if (first_conjunct) {
          first_conjunct = 0;
        }
        else {
          fprintf(f," AND ");
        }
        fprintf(f,"C%d <= %d",tinv[i*8+7].clock,tinv[i*8+7].bound);
      }
    }
  }
  if (first_conjunct) {
    fprintf(f,"true");
  }
  fprintf(f,"\n");
}

void 
fprint_state_header(FILE *f, state_t *s) {
  fprintf(f,"\nstate: %d\ninvar: ", s->number);
  fprint_invariant(f,(state_vector_t *)s);
  fprintf(f,"trans: \n");
}

void
print_state_header(state_t *s) {
  fprint_state_header(stdout,s);
}

void 
transition(state_vector_t *s1, label_t *lab, state_vector_t *s2) {
  state_t *s = (state_t *)s2;

  s->number = global_state_number;
  if (hstore2(loc_table,(char *)s2,size_state(),(char *)&(s->number),sizeof(int))) {
    enqueue(q,s);
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
#ifdef TG
  fprint_label(graph_output,lab);
  fprintf(graph_output,"goto %d\n",s->number);
#endif
  global_transition_number += 1;
}


int 
main () {
  label_t label;
  state_t *current_state = (state_t *)emalloc(sizeof(state_t));
  state_t *new_state = (state_t *)emalloc(sizeof(state_t));

  q = new_queue(sizeof(state_t));
  data = new_stack(sizeof(data_env_t));
  hinit(loc_table,SSIZE);
#ifdef TG
  graph_output = fopen("/tmp/graph.tg","w");  
  fprintf(graph_output,"#states               %8d\n", global_state_number);
  fprintf(graph_output,"#trans                %8d\n", global_transition_number);
  fprintf(graph_output,"#clocks               %8d\n", N_CLOCKS);
  fprint_clock_names(graph_output); 
  fprintf(graph_output,"\n\n\n");
#endif
  start_state((state_vector_t *)current_state);
#ifdef VVERBOSE
  printf("state %6d : ",global_state_number);
  print_state_vector_bytes((state_vector_t *)current_state);
  printf("\n");
#endif
  current_state->number = global_state_number++;
  hstore2(loc_table,(char *)current_state,size_state(),(char *)&(current_state->number),sizeof(int));
  enqueue(q,current_state);
  while (is_non_empty_q(q)) {
    dequeue(q,current_state);
#ifdef TG
    fprint_state_header(graph_output,current_state);
#endif
    iterate_state((state_vector_t *)current_state,&label,(state_vector_t *)new_state,transition);
  }
#ifdef VERBOSE
  printf("#state vector bytes   %8d\n", size_state());
  print_state_vector_boundaries((state_vector_t *)current_state);
  printf("hash conflicts (resolved) %g\n",loc_table->hcmp);
#endif
  printf("#states               %8d\n", global_state_number);
  printf("#trans                %8d\n", global_transition_number);
  printf("#clocks               %8d\n", N_CLOCKS);
  print_clock_names (); printf("\n\n\n");
#ifdef TG
  fflush(graph_output);
  rewind(graph_output);
  fprintf(graph_output,"#states               %8d\n", global_state_number);
  fprintf(graph_output,"#trans                %8d\n", global_transition_number);
  fclose(graph_output);
#endif
#ifdef MEMCNT
  printf("%-6.3f memory usage (Mbyte)\n\n",memcnt/1000000.);
#endif
  exit(0); 
}
