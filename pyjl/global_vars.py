# Decorator Names
RESUMABLE = "resumable"
CHANNELS = "channels"
REMOVE_NESTED = "remove_nested"
OFFSET_ARRAYS = "offset_arrays"
JL_CLASS="jl_class"

# Flags
USE_MODULES = "use_modules"
FIX_SCOPE_BOUNDS="fix_scope_bounds"
LOOP_SCOPE_WARNING = "loop_scope_warning"
OBJECT_ORIENTED = "oop"
OOP_NESTED_FUNCS = "oop_nested_funcs"

# List holding all global flags
GLOBAL_FLAGS = [USE_MODULES, FIX_SCOPE_BOUNDS,
    LOOP_SCOPE_WARNING, OBJECT_ORIENTED, 
    OOP_NESTED_FUNCS]

###################################
# Julia Types
DEFAULT_TYPE = "Any"
NONE_TYPE = "nothing"

###################################
# Helpers
COMMON_LOOP_VARS = ["v", "w", "x", "y", "z"]
SEP = ["{", "}"]