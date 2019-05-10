module lang::javascript::EvalJS

@javaClass{lang.javascript.EvalJS}
java str evalJS(loc script, str command);

@javaClass{lang.javascript.EvalJS}
java str evalJS(str command);


alias JSResult = tuple[map[str, value] bindings, value val];

@javaClass{lang.javascript.EvalJS}
java JSResult evalJS(str command, map[str, value] bindings);

@javaClass{lang.javascript.EvalJS}
java void sleep(int millis);
