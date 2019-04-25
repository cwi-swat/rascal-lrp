module lang::lrp::Eval


import lang::lrp::Syntax;
import lang::javascript::EvalJS;
import DateTime;
import String;
import ParseTree;
import IO;


// there's no shadowing so the whole state 
// can be represented as a single map 
alias Env = map[str var, value val];

alias RT
  = tuple[
   lrel[loc machine, loc state] active,
   Env env,
   map[loc, datetime] timers, 
   void(value) log
];


RT init(start[LRP] lrp) 
  = <[<m@\loc, s@\loc>], evalVars(lrp.top.globals, ()), (), println>
  when
    Machine m := lrp.top.machine, 
    Decl s <- m.decls, s is state, s.name == lrp.top.spawn.initial;

   
RT step(start[LRP] lrp, RT rt) = run(lrp.top.machine, rt);

// Step 2
RT run(Machine m, RT rt) = run(m, s, rt)
  when
    loc currentState := rt.active[0].state,
    Decl s <- m.decls, s is state, s@\loc == currentState;
    

RT run(Machine parent, Decl current, RT rt) {
   rt.timers = startTimers(parent, rt);
   rt.log("Evaling contents: <current.contents>");
   rt = evalContents(current.contents, current, onEntry, rt);
   return fire(parent, current, rt);
}

map[loc,datetime] startTimers(Machine m, RT rt) 
  = rt.timers + ( d@\loc: n | Decl d <- m.decls, d is timed )
  when datetime n := now();

// Step 3/4
RT fire(Machine m, Decl current, RT rt) {
  list[Decl] transitions = outgoing(m, current);
  if (Decl t <- transitions, evalGuard(t, m, rt), Decl s <- m.decls, s is state, s.name == t.to) {
    rt.log("transitioning to <t.to>");
    rt = evalContents(current.contents, current, onExit, rt);
    rt.active = rt.active[0..-1] + [<m@\loc, s@\loc>];
    return rt;
  }
  return evalContents(current.contents, current, running, rt);
}

bool evalGuard(Decl trans, Machine m, RT rt) {
  if (trans is epsilon) {
    rt.log("epsilon trans <trans>");
    return true;
  }
  if (trans is timed, int delta := evalJS("<trans.time>", rt.env).val) {
    rt.log("timed trans <trans> at <delta>");
    datetime started = rt.timers[trans@\loc];
    bool b = incrementMilliseconds(started, delta) > now();
    rt.log("guard is <b>");
    return b;   
  }
  if ((Decl)`event <Id e> <Expression cond>;` <- m.decls, e == trans.event) {
    return bool b := evalJS("<cond>", rt.env).val && b;
  }
  throw "invalid transition <trans>";
}

list[Decl] outgoing(Machine m, Decl s)
  = [ d | Decl d <- m.decls, d has from, d.from == s.name ]
  + [ d | Decl d <- m.decls, d is wildcard ];


RT running((Contents)`running {<Statement* js>}`, Decl parent, RT rt)
  = rt[env = evalJS("{<js>}", rt.env).bindings];

RT running((Contents)`<Machine m>`, Decl parent, RT rt)
  = fire(m, parent, rt);


RT onEntry((Contents)`on entry {<Statement* js>}`, Decl parent, RT rt)
  = rt[env = evalJS("{<js>}", rt.env).bindings];

RT onEntry((Contents)`on entry spawn <Id m> <Id s>`, Decl parent, RT rt)
  = run(machine, state, rt[active = rt.active + [<machine@\loc, state@\loc>]])
  when 
    Machine machine := lookupMachine(parent, m),
    Decl state <- machine.decls, state.name == s; 

RT onExit((Contents)`on exit {<Statement* js>}`, Decl parent, RT rt) {
  if (Machine machine := lookupMachine(parent, m), Decl state <- machine.decls, 
     state is state,
     rt.active[-1] == <machine@\loc, state@\loc>) {
    rt = evalContents(state.contents, state, onExit, rt);   
  }
  rt.env = evalJS("{<js>}", rt.env).bindings;
  rt.active = rt.active[0..-1];
  return rt;
}
     

Machine lookupMachine((Decl)`state <Id _> <Machine m>`, Id x) = m
  when m.name == x;
  
Machine lookupMachine((Decl)`state <Id _> {<Content* cs>}`, Id x) = m
  when Machine m <- cs, m.name == x;
  

RT evalContents((Contents)`{<Contents* cs>}`, Decl s, RT(Contents, Decl, RT) eval, RT rt)
  = ( rt | evalContents(c, s, eval, it) | Contents c <- cs );

RT evalContents((Contents)`;`, Decl s, RT(Contents, Decl, RT) eval, RT rt)
  = rt;
  
default Env evalContents(Contents c, Decl s, RT(Contents, Decl, RT) eval, RT rt)
  = eval(c, s, rt);


Env evalVars(Decl* decls, Env env)
  = ( env | evalVar(d, it) | Decl d <- decls, d is var );
  
Env evalVar((Decl)`var <Id x> := <Expression e>;`, Env env)
  = env + ("<x>": evalJS("<e>", env).val);
  

