value : Type
comp : Type
bool : Type

u: value
pair: value -> value -> value
inj: bool -> value -> value
thunk: comp -> value

cu: comp
force: value -> comp
lambda: (value -> comp) -> comp
app: comp -> value -> comp
tuple: comp -> comp -> comp
ret: value -> comp
letin: comp -> (value -> comp) -> comp
proj: bool -> comp -> comp
caseZ: value -> comp
caseS: value -> (value -> comp) -> (value -> comp) -> comp
caseP: value -> (value -> value -> comp) -> comp
tock: comp.
