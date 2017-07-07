

typedef struct {
  uint _VAR__;
} data_env_t;

void
OP_ReadSensor(data_env_t *env, stack_t *data) {
  push(data,env);
}