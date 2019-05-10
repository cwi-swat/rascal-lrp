module lang::lrp::Eval


import lang::lrp::Syntax;
import lang::javascript::EvalJS;
import DateTime;
import String;
import ParseTree;
import IO;


/*

- variables only initialized at the very beginning
- active machine/state list should be a tree (or array of stacks when concurrency only at toplevel)
  (assume state names are unique)
- reset timers indeed before onEntry
- make identification of machine/state stuff location independent

*/

// there's no shadowing so the whole state 
// can be represented as a single map 
alias Heap = map[str var, value val];

alias Timers = rel[str from, str to, datetime now];

alias Active = tuple[str state, Timers timers];

alias Thread = list[Active]; // stack 

alias RT = tuple[map[str machine, Thread thread] threads, Heap heap];

// Helper functions

void run(loc l, int delay = 1000) {
  run(parse(#start[LRP], l), delay = delay);
}

void run(start[LRP] lrp, int delay = 1000) {
  rt = initialize(lrp);
  while (true) {
    rt = loop(lrp, rt);
    sleep(delay);
  }
}



// System-wide functions

RT initialize(start[LRP] lrp) {
  RT rt = <(), initVars(lrp)>;
  for (Machine m <- lrp.top.machines, (Code)`spawn <Id x> <Id s>` <- lrp.top.spawns, x == m.name) {
    <rt.threads["<x>"], rt.heap> = makeActive(m, "<s>", rt.heap);
  }
  return rt;    
}

RT loop(start[LRP] lrp, RT rt) {
  for (str tid <- rt.threads) {
    <rt.threads[tid], rt.heap> = fire(lookupMachine(lrp, tid), rt.threads[tid], rt.heap);
  }
  return rt;
} 


// Per thread functions

tuple[Thread, Heap] fire(Machine m, Thread me, Heap heap) {
  Decl current = lookupState(m, me[0].state);
  if (Decl t <- outgoing(m, current), evalGuard(t, m, heap)) {
    heap = onExit(current, me, heap);
    return makeActive(m, "<t.to>", heap);
  }
  return running(current, me, heap);
}


bool evalGuard(Decl trans, Machine m, Thread me, Heap heap) {
  if (trans is epsilon) {
    return true;
  }
  if ((Decl)`on time <Expression t> <Id from> -\> <Id to>` := trans, int delta := evalJS("<t>", heap).val) {
    datetime started = lookupTimer(me[0].timers, from, to);
    return incrementMilliseconds(started, delta) < now();
  }
  if ((Decl)`event <Id e> <Expression cond>;` <- m.decls, e == trans.event) {
    return (bool b := evalJS("<cond>", heap).val) && b;
  }
  throw "invalid transition <trans>";
}

tuple[Thread, Heap] makeActive(Machine m, str state, Heap heap) {
  Timers timers = initTimers(m);
  <nested, heap> = onEntry(lookupState(m, state), heap);
  return <[<state, timers>] + nested, heap>;
}

tuple[Thread, Heap] onEntry(Decl state, Heap heap) {
  top-down-break visit (state) {
    case (Contents)`on entry {<Statement* js>}`:
      return <[], evalJS("{<js>}", heap).bindings>;
    case (Contents)`on entry spawn <Id m> <Id s>`:
      return makeActive(lookupMachine(parent, m), "<s>", heap);
  }
  return <[], heap>;
}


tuple[Thread, Heap] running(Decl state, Thread me, Heap heap) {
  assert me[0].state == "<state.name>";
  
  top-down-break visit (state) {
    case (Contents)`running {<Statement* js>}`: heap = evalJS("{<js>}", heap).binding;
  } 
  
  // NB: this really depends on uniqueness of state names across machines
  if (size(me) > 1, /Machine m := state, Decl d <- m.decls, d is state, "<d.name>" == me[1].state) {
    <nested, heap> = fire(m, me[1..], heap);
    return <[me[0], *nested], heap>;
  } 
  
  return <me, heap>;
}

Heap onExit(Decl state, Thread me, Heap heap) {
  // NB: this really depends on uniqueness of state names across machines
  if (size(me) > 1, /Machine m := state, Decl d <- m.decls, d is state, "<d.name>" == me[1].state) {
    heap = onExit(d, m[1..], heap);
  } 
  
  top-down-break visit (state) {
    case (Contents)`on exit {<Statement* js>}`: heap = evalJS("{<js>}", heap).bindings;
  }
  
  return heap;
}

// Utils

Heap initVars(start[LRP] lrp) 
  = ( () | it +  ("<x>": evalJS("<e>", it).val) | /(Decl)`var <Id x> := <Expression e>;` := lrp ); 

Timers initTimers(Machine m) 
  = { <"<from>", "<to>", now()> |  (Decl)`on time <Expression _> <Id from> -\> <Id to>` <- m.decls };

datetime lookupTimer(Timers ts, Id from, Id to) = dt
  when <str f, str t, datetime dt> <- ts, "<from>" ==f, "<to>" == t;

list[Decl] outgoing(Machine m, Decl s)
  = [ d | Decl d <- m.decls, (d has from && d.from == s.name) || d is wildcard ];

Machine lookupMachine(start[LRP] lrp, str tid) = m
  when Machine m <- lrp.top.machines, "<m.name>" == tid;

Decl lookupState(Machine m, str name) = s
  when Decl s <- m.decls, s is state, "<s.name>" == name;



