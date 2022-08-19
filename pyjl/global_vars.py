# Decorator Names
RESUMABLE = "resumable"
CHANNELS = "channels"
OFFSET_ARRAYS = "offset_arrays"
JL_CLASS="jl_class"
OOP_CLASS="oop_class"
PARAMETERIZED="parameterized"

# Flags
USE_RESUMABLES = "use_resumables"
LOWER_YIELD_FROM = "lower_yield_from"
USE_MODULES = "use_modules"
FIX_SCOPE_BOUNDS="fix_scope_bounds"
LOOP_SCOPE_WARNING = "loop_scope_warning"
OBJECT_ORIENTED = "oop"
OOP_NESTED_FUNCS = "oop_nested_funcs"
USE_GLOBAL_CONSTANTS = "use_global_constants"
ALLOW_ANNOTATIONS_ON_GLOBALS = "allow_annotations_on_globals"
REMOVE_NESTED_RESUMABLES = "remove_nested_resumables"

# Decorators and Flags
REMOVE_NESTED = "remove_nested"

# List holding all global flags
GLOBAL_FLAGS = [USE_MODULES, FIX_SCOPE_BOUNDS,
    LOOP_SCOPE_WARNING, OBJECT_ORIENTED, 
    OOP_NESTED_FUNCS, USE_GLOBAL_CONSTANTS]

###################################
# Julia Types
DEFAULT_TYPE = "Any"
NONE_TYPE = "nothing"

###################################
# Helpers
COMMON_LOOP_VARS = ["v", "w", "x", "y", "z"]
SEP = ["{", "}"]