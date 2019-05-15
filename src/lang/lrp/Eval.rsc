module lang::lrp::Eval


import lang::lrp::Syntax;
import lang::javascript::EvalJS;
import DateTime;
import String;
import ParseTree;
import IO;
import List;

/*

- Logical time

*/

// there's no shadowing so the whole state 
// can be represented as a single map 
alias Heap = map[str var, value val];

//alias Timers = rel[str from, str to, datetime now];
alias Timers = rel[str from, str to, int now];

alias Active = tuple[str state, Timers timers];

alias Thread = list[Active]; // stack 

alias RT = tuple[map[str machine, Thread thread] threads, Heap heap];

// Helper functions

void run(loc l, int step = 1000, int delay = 1000) {
  run(parse(#start[LRP], l), step = step, delay = delay);
}

void printRT(RT rt, int time) {
  println("RUNTIME @ <time>");
  println("  HEAP:");
  for (str x <- rt.heap) {
    println("    <x>: <rt.heap[x]>"); 
  }
  println(" THREADS: ");
  for (str tid <- rt.threads) {
    println("    <tid>: <intercalate("/", [ s | <str s, _> <- rt.threads[tid] ])>");
    for (<str s, Timers ts> <- rt.threads[tid]) {
      println("      <s>: <intercalate(", ", [ "<f>-\><t> @ <d>" | <str f, str t, int d> <- ts ])>");
    }
  }
}

void run(start[LRP] lrp, int step = 1000, int delay = 1000) {
  int time = 0;
  rt = initialize(lrp, time);
  while (true) {
    printRT(rt, time);
    rt = loop(lrp, rt, time);
    sleep(delay);
    time += step;
  }
}



// System-wide functions

RT initialize(start[LRP] lrp, int time) {
  RT rt = <(), initVars(lrp)>;
  for ((Code)`spawn <Id x> <Id s>` <- lrp.top.spawns) {
    str m = "<x>";
    <rt.threads[m], rt.heap> = makeActive(lookupMachine(lrp, m), "<s>", rt.heap, time);
  }
  return rt;    
}

RT loop(start[LRP] lrp, RT rt, int time) {
  for (str tid <- rt.threads) {
    <rt.threads[tid], rt.heap> = fire(lookupMachine(lrp, tid), rt.threads[tid], rt.heap, time);
  }
  return rt;
} 


// Per thread functions

tuple[Thread, Heap] makeActive(Machine m, str state, Heap heap, int time) {
  Timers timers = initTimers(m, time);
  <nested, heap> = onEntry(lookupState(m, state), heap, time);
  return <[<state, timers>] + nested, heap>;
}

tuple[Thread, Heap] fire(Machine m, Thread me, Heap heap, int time) {
  Decl current = lookupState(m, me[0].state);
  if (Decl t <- outgoing(m, current), evalGuard(t, m, me, heap, time)) {
    heap = onExit(current, me, heap);
    return makeActive(m, "<t.to>", heap, time);
  }
  return running(current, me, heap, time);
}


bool evalGuard(Decl trans, Machine m, Thread me, Heap heap, int time) {
  if (trans is epsilon) {
    return true;
  }
  
  if ((Decl)`on time <Expression t> <Id from> -\> <Id to>` := trans, num delta := evalJS("<t>", heap).val) {
    int started = lookupTimer(me[0].timers, from, to);
    //return now() > incrementMilliseconds(started, delta);
    return time > started + delta;
  }
  
  // Covers both wildcard and ordinary transitions
  if ((Decl)`event <Id e> <Expression cond>;` <- m.decls, e == trans.event) {
    return (bool b := evalJS("<cond>", heap).val) && b;
  }
  
  throw "invalid transition <trans>";
}


tuple[Thread, Heap] onEntry(Decl state, Heap heap, int time) {
  list[Contents] cs = contentsOf(state);

  if ((Contents)`on entry {<Statement* js>}` <- cs) {
    return <[], evalJS("{<js>}", heap).bindings>;
  }
  
  if ((Contents)`on entry spawn <Id m> <Id s>` <- cs) {
    return makeActive(lookupMachine(state, "<m>"), "<s>", heap, time);
  }

  return <[], heap>;
}


tuple[Thread, Heap] running(Decl state, Thread me, Heap heap, int time) {
  for ((Contents)`running {<Statement* js>}` <- contentsOf(state)) {
    heap = evalJS("{<js>}", heap).bindings;
  } 
  
  if ((Contents)`<Machine m>` <- contentsOf(state), hasChild(m, me)) {
    <nested, heap> = fire(m, me[1..], heap, time);
    return <[me[0], *nested], heap>;
  } 
  
  return <me, heap>;
}


Heap onExit(Decl state, Thread me, Heap heap) {
  if ((Contents)`<Machine m>` <- contentsOf(state), hasChild(m, me)) {
    heap = onExit(lookupState(m, me[1].state), me[1..], heap);
  } 
  
  for ((Contents)`on exit {<Statement* js>}` <- contentsOf(state)) {
    heap = evalJS("{<js>}", heap).bindings;
  }
  
  return heap;
}

// Utils

list[Decl] outgoing(Machine m, Decl s)
  = [ d | Decl d <- m.decls, (d has from && d.from == s.name) || d is wildcard ];

list[Contents] contentsOf((Decl)`state <Id _> {<Contents* cs>}`) 
  = [ c | Contents c <- cs ];

default list[Contents] contentsOf(Decl s) = [s.contents];

Heap initVars(start[LRP] lrp) 
  = ( () | it +  ("<x>": evalJS("<e>", it).val) | /(Decl)`var <Id x> := <Expression e>;` := lrp ); 

Timers initTimers(Machine m, int time) 
  = { <"<from>", "<to>", time> |  (Decl)`on time <Expression _> <Id from> -\> <Id to>` <- m.decls };

int lookupTimer(Timers ts, Id from, Id to) = dt
  when <str f, str t, int dt> <- ts, "<from>" == f, "<to>" == t;

Machine lookupMachine(start[LRP] lrp, str tid) = m
  when Machine m <- lrp.top.machines, "<m.name>" == tid;

Machine lookupMachine(Decl state, str tid) = m
  when (Contents)`<Machine m>` <- contentsOf(state), "<m.name>" == tid;

bool hasState(Machine m, str name) = Decl s <- m.decls && isNamedState(s, name);

Decl lookupState(Machine m, str name) = s
  when Decl s <- m.decls, isNamedState(s, name);

bool isNamedState(Decl d, str name) = d is state && "<d.name>" == name;

bool hasChild(Machine m, Thread me) = size(me) > 1 && hasState(m, me[1].state);


