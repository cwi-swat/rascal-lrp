package lang.javascript;

import java.io.IOException;
import java.io.Reader;

import javax.script.Bindings;
import javax.script.ScriptContext;
import javax.script.ScriptEngine;
import javax.script.ScriptEngineManager;
import javax.script.ScriptException;

import org.rascalmpl.interpreter.utils.RuntimeExceptionFactory;
import org.rascalmpl.uri.URIResolverRegistry;

import io.usethesource.vallang.IBool;
import io.usethesource.vallang.IInteger;
import io.usethesource.vallang.IMap;
import io.usethesource.vallang.IMapWriter;
import io.usethesource.vallang.IReal;
import io.usethesource.vallang.ISourceLocation;
import io.usethesource.vallang.IString;
import io.usethesource.vallang.ITuple;
import io.usethesource.vallang.IValue;
import io.usethesource.vallang.IValueFactory;

public class EvalJS {
	private final IValueFactory values;

	private final ScriptEngineManager mgr;
	private final ScriptEngine engine;
	
	public EvalJS(IValueFactory values) {
		super();
		this.values = values;
		this.mgr = new ScriptEngineManager();
		this.engine = mgr.getEngineByName("nashorn");
 	}

	public IString evalJS(ISourceLocation script, IString command) {
		try (Reader reader = URIResolverRegistry.getInstance().getCharacterReader(script)) {
			engine.eval(reader);
			Object result = engine.eval(command.getValue());
			return values.string(result.toString());
		} catch (ScriptException e) {
			throw RuntimeExceptionFactory.io(values.string(e.getMessage()), null, null);
		} catch (IOException e) {
			throw RuntimeExceptionFactory.io(values.string(e.getMessage()), null, null);
		}
	}

	public ITuple evalJS(IString code, IMap env) {
		Bindings bindings = engine.createBindings();
		for (IValue k: env) {
			IValue v = env.get(k);
			bindings.put(((IString)k).getValue(),  ivalue2js(v));
		}
		engine.setBindings(bindings, ScriptContext.ENGINE_SCOPE);
		Object result = null;
		try {
			result = engine.eval(code.getValue());
		} catch (ScriptException e) {
			throw RuntimeExceptionFactory.io(values.string(e.getMessage()), null, null);
		}
		IMapWriter w = values.mapWriter();
		Bindings newBindings = engine.getBindings(ScriptContext.ENGINE_SCOPE);
		for (String k: newBindings.keySet()) {
			Object v = newBindings.get(k);
			w.put(values.string(k), js2ivalue(v));
		}
		return values.tuple(w.done(), js2ivalue(result));
	}
	
	private Object ivalue2js(IValue v) {
		if (v instanceof IReal) {
			return ((IReal)v).doubleValue();
		}
		if (v instanceof IInteger) {
			return ((IInteger)v).intValue();
		}
		if (v instanceof IString) {
			return ((IString)v).getValue();
		}
		if (v instanceof IBool) {
			return ((IBool)v).getValue();
		}
		throw RuntimeExceptionFactory.io(values.string("unsupported value: " + v.getType()), null, null);
	}
	
	private IValue js2ivalue(Object v) {
		if (v == null) {
			throw RuntimeExceptionFactory.io(values.string("null not supported"), null, null);
		}
		if (v instanceof String) {
			return values.string((String)v);
		}
		if (v instanceof Integer) {
			return values.integer((Integer)v);				
		}
		if (v instanceof Double) {
			return values.real((Double)v);				
		}
		if (v instanceof Boolean) {
			return values.bool((Boolean)v);				
		}
		throw RuntimeExceptionFactory.io(values.string("unsupported object: " + v.getClass().getName()), null, null);
	}
	
	public IString evalJS(IString command) {
		try {
			return values.string(engine.eval(command.getValue()).toString());
		} catch (ScriptException e) {
			throw RuntimeExceptionFactory.io(values.string(e.getMessage()), null, null);
		}
	}
	
	public void sleep(IInteger millis) {
		try {
			Thread.sleep(millis.longValue());
		} catch (InterruptedException e) {
			return;
		}
	}
	
	
	
}