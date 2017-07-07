

typedef struct {
  uint _VAR__;
} data_env_t;

void
OP_ID(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_AdjustValve(data_env_t *env, stack_t *data) {
  push(data,env);
}