module lang::lrp::Eval


import lang::lrp::Syntax;
import lang::javascript::EvalJS;
import DateTime;
import String;
import ParseTree;


// there's no shadowing so the whole state 
// can be represented as a single map 
alias Env = map[str var, value val];

alias RT
  = tuple[
   lrel[loc machine, loc state] active,
   Env env,
   map[loc, datetime] timers
];

  

RT init(start[LRP] lrp) 
  = <
    [<"<lrp.top.spawn.machine>", "<lrp.top.spawn.initial>">],
    evalVars(lrp.top.globals, ()),
    ()
   >;
  
  
   
RT run(start[LRP] lrp, RT rt) = run(lrp.machine, rt);

// Step 2
RT run(Machine m, RT rt) {
  loc currentState = rt.active[0].state;
  if (State s <- m.decls, s@\loc == currentState) {
    return run(m, s, rt);
  }
}

RT run(Machine parent, State current, RT rt) {
   rt.timers = startTimers(parent, rt);
   rt = evalContents(current.contents, onEntry, rt);
   return fire(parent, current, rt);
}

map[loc,datetime] startTimers(Machine m, RT rt) 
  = rt.timers + ( d@\loc: evalJS("<d.time>", rt.env).val | Decl d <- m.decls, d is timed );

// Step 3/4
RT fire(Machine m, State current, RT rt) {
  list[Decl] transitions = outgoing(parent, current);
  if (Decl t <- transitions, evalGuard(t, m, rt), State s <- m.decls, s.name == t.to) {
    rt = evalContents(current.contents, onExit, rt);
    rt.active += [<m@\loc, s@\loc>];
    return rt;
  }
  return evalContents(current.contents, running, rt);
}

bool evalGuard(Decl trans, Machine m, RT rt) {
  if (trans is epsilon) {
    return true;
  }
  if (trans is timed) {
    datetime started = rt.timers[trans@\loc];
    num x = evalJS("<trans.time>", rt.env).val;
    return now - started > x; // TODO: duration unpacking
  }
  if ((Decl)`event <Id e> <Expression cond>` <- m.decls, e == trans.event) {
    return bool b := evalJS("<cond>", rt.env).val && b;
  }
}

list[Decl] outgoing(Machine m, State s)
  = [ d | Decl d <- m.decls, d has from, d.from == s.name ]
  + [ d | Decl d <- m.decls, d is wildcard ];


RT running((Contents)`running {<Statement* js>}`, State parent, RT rt)
  = rt[env = evalJS("{<js>}", rt.env).bindings];

RT running((Contents)`<Machine m>`, State parent, RT rt)
  = fire(m, parent, rt);


RT onEntry((Contents)`on entry {<Statement* js>}`, State parent, RT rt)
  = rt[env = evalJS("{<js>}", rt.env).bindings];

RT onEntry((Contents)`on entry spawn <Id m> <Id s>`, State parent, RT rt)
  = run(machine, state, rt[active = rt.active + [<machine@\loc, state@\loc>]])
  when 
    Machine machine := lookupMachine(parent, m),
    State state <- machine.decls, state.name == s; 

RT onExit((Contents)`on exit {<Statement* js>}`, State parent, RT rt) {
  if (Machine machine := lookupMachine(parent, m), State state <- machine.decls,
     rt.active[-1] == <machine@\loc, state@\loc>) {
    rt = evalContents(state.contents, onExit, rt);   
  }
  rt.env = evalJS("{<js>}", rt.env).bindings;
  rt.active = rt.active[0..-1];
  return rt;
}
     

Machine lookupMachine((State)`state <Id _> <Machine m>`, Id x) = m
  when m.name == x;
  
Machine lookupMachine((State)`state <Id _> {<Content* cs>}`, Id x) = m
  when Machine m <- cs, m.name == x;
  

RT evalContents((Contents)`{<Contents* cs>}`, Env(Contents, State, RT) eval, RT rt)
  = ( rt | evalContents(c, eval, it) | Contents c <- cs );

RT evalContents((Contents)`;`, Env(Contents, State, RT) eval, RT rt)
  = rt;
  
default Env evalContents(Contents c, Env(Contents, Env) eval, env)
  = eval(c, env);


Env evalVars(Decl* decls, Env env)
  = ( env | evalVar(d, it) | Decl d <- decls, d is var );
  
Env evalVar((Decl)`var <Id x> := <Expression e>;`, Env env)
  = env + ("<x>": evalJS("<e>", env).val);
  

