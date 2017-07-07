typedef struct {
  uchar _VAR_x;
} data_env_t;

void
OP_ID(data_env_t *env, stack_t *data) {
  data_env_t temp = *env;
  push(data,&temp);
}

void
OP_xone(data_env_t *env, stack_t *data) {
  data_env_t temp = *env;
  temp._VAR_x = 1;
  push(data,&temp);
}

void
OP_incx(data_env_t *env, stack_t *data) {
  data_env_t temp = *env;
  temp._VAR_x += 1;
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

int
PRED_isxfive(data_env_t *env) {
  return (env->_VAR_x == 5);
}
