

typedef struct {
  uint _VAR__;
} data_env_t;

void
OP_a(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_b(data_env_t *env, stack_t *data) {
  push(data,env);
}

int
PRED_stop(data_env_t *env) {
  return 1;
}