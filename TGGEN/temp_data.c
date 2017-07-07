typedef struct {
  uint _VAR__;
} data_env_t;

void
OP_ID(data_env_t *env, stack_t *data) {
  data_env_t temp = *env;
  push(data,&temp);
}

int
PRED___true(data_env_t *env) {
  return(1);
}

int
PRED___false(data_env_t *env) {
  return(0);
}