#if !defined REFL_GENERATE && !defined REFL_PLUGIN_LOADED
#define REFL_CONC(arg) REFLG_ ## arg
#define REFL_PASS(arg) REFL_CONC(arg)
REFL_PASS(REFL_CLASS)
#undef REFL_CONC
#undef REFL_PASS
#endif
#undef REFL_CLASS
