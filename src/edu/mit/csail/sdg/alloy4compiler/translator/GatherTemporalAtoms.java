package edu.mit.csail.sdg.alloy4compiler.translator;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;

import java.util.*;


/*
* This class aims to gather all atoms presented on all xml files during the vizualation preparatio.
* As the xml's are created, this class fill the exprToAtoms --  make a mapping between a Expr and all atoms presented in all xml files for such Expr.
 * Basically, this class is composed by two sub-classes -- Tuple and TupleSet, that are a replication of the original classes resented on the Kodkod.
 * Obviously, for each Expr is assgned a TupleSet, in turn, this one is a set of Tuple
 *
 *
* */

public class GatherTemporalAtoms {
    public Map<Expr,TupleSet> exprToAtoms;


    public GatherTemporalAtoms() {
        this.exprToAtoms = new HashMap<Expr,TupleSet>();
    }

    public void addTupleSetToExprx(Expr expr,TupleSet s){
        if (!this.exprToAtoms.containsKey(expr))  this.exprToAtoms.put(expr, s);
        else this.exprToAtoms.put(expr, ((TupleSet)this.exprToAtoms.get(expr)).addTupleSetAll(s));

    }

    public void addTupleSetToExprx(Expr expr){
        if (!this.exprToAtoms.containsKey(expr))  this.exprToAtoms.put(expr, this.temporaryTupleSet);
        else this.exprToAtoms.put(expr, ((TupleSet)this.exprToAtoms.get(expr)).addTupleSetAll(this.temporaryTupleSet));

    }



    //-------------------------------------
    private Tuple temporaryTuple;
    public void addAtomInTuple(Object atom){
            this.temporaryTuple.addAtom(atom);
    }
    public void initTuple(){
        this.temporaryTuple =  new Tuple();
    }

    //-------------------------------------

    private TupleSet temporaryTupleSet;
    public void addAtomInTupleSet(Tuple atom){
        this.temporaryTupleSet.addTuple(atom);
    }

    public void addAtomInTupleSet(){
        this.temporaryTupleSet.addTuple(this.temporaryTuple);
    }
    public void initTupleSet(){
        this.temporaryTupleSet =  new TupleSet();
    }


    public class Tuple{
        private List<Object> tuple;

        public Tuple() { this.tuple =  new ArrayList<>();}

        public Tuple(List<Object> tuple) {
            this.tuple = tuple;
        }

        public Tuple(Collection c) {
            this.tuple =  new ArrayList<>();
            this.tuple.addAll(c);
        }

        public void addAtom(Object atom){
            this.tuple.add(atom);
        }

        @Override
        public String toString() {
            return this.tuple.toString();
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + this.tuple.hashCode();
            return result;
        }
        @Override
        public boolean equals(Object obj) {
            return true;
        }

        public List<Object> getTuple() {
            return tuple;
        }
    }


    public class TupleSet{
        private List<Tuple> tupleSet;

        public List<Tuple> getTupleSet() {
            return tupleSet;
        }

        public TupleSet() {
            this.tupleSet =  new ArrayList<>();
        }

        public TupleSet addTupleSetAll(TupleSet s){
            this.tupleSet.addAll(s.getTupleSet());
            return this;
        }

        public void addTuple(Tuple tuple){
            this.tupleSet.add(tuple);
        }

        public TupleSet(Collection tuples) {
            this.tupleSet =  new ArrayList<>();
            this.tupleSet.addAll(tuples);
        }

        public TupleSet(Tuple tuple) {
            this.tupleSet =  new ArrayList<>();
            addTuple(tuple);
        }

        @Override
        public String toString() {
            return this.tupleSet.toString();
        }
    }

    public void optimizeTemporalAtoms(){
        Map temporalAtoms =  new HashMap<Expr,TupleSet>();
        for(Expr expr : this.exprToAtoms.keySet()){
            if (expr instanceof Sig){
                Set s =  new HashSet();
                for (Tuple t :  this.exprToAtoms.get(expr).tupleSet) for (Object o : t.tuple) s.add(o);
                Tuple tuple = new Tuple(s);
                temporalAtoms.put(expr,new TupleSet(tuple));
            }else{// if (expr instanceof Sig.Field){
                Collection<Tuple> uniqueBlogs =  new HashSet<>();
                for (Tuple t :  this.exprToAtoms.get(expr).tupleSet) uniqueBlogs.add(t);
                temporalAtoms.put(expr,new TupleSet(uniqueBlogs));
            }

        }
       this.exprToAtoms =  temporalAtoms;
    }

    public TupleSet evalExpr(Expr expr){
        return this.exprToAtoms.get(expr);
    }

    @Override
    public String toString() {
        StringBuilder s = new StringBuilder("");
        for (Expr expr : this.exprToAtoms.keySet()){
            s.append(expr.toString()+" :\n->"+this.exprToAtoms.get(expr).toString()+"\n----------------------------\n");
        }
        return s.toString();

    }
}
