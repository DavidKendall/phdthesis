typedef struct {
  uchar _VAR__  : 1;
  uchar _VAR_v1 : 2;
  uchar _VAR_v2 : 2;
} data_env_t;

static data_env_t temp;
 
void
OP_ReadWaterLevel(data_env_t *env, stack_t *data) {
  temp = *env;
  temp._VAR_v1 = 0; 
  push(data,&temp);
  temp._VAR_v1 = 1; 
  push(data,&temp);
  temp._VAR_v1 = 2; 
  push(data,&temp);
}

void
OP_ID(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_SensorFailed(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_InitSensor(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_InitPump(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_InitController(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_C_ReadyDelay(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_WL_ReadyPeriod(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_WL_NormalPeriod(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_P_ReadyPeriod(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_P_NormalPeriod(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_Timeout(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_PumpOn(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_PumpOff(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_EndSetPump(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_TestLevel(data_env_t *env, stack_t *data) {
  push(data,env);
}

int
PRED_LevelOk(data_env_t *env) {
  return (env->_VAR_v2 == 1);
}

int
PRED_LevelLow(data_env_t *env) {
  return (env->_VAR_v2 == 0);
}

int
PRED_LevelHigh(data_env_t *env) {
  return (env->_VAR_v2 == 2);
}

int
PRED___true(data_env_t *env) {
  return (1);
}

int
PRED___false(data_env_t *env) {
  return (0);
}



