// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "Enumerators.dfy"

// An example of an enumerator that traverses the sub-values in 
// an algebraic datatype value.
module DatatypeEnumerator {

  import opened Enumerators
  
  datatype Tree<T> = Node(left: Tree<T>, value: T, right: Tree<T>) | Nil

  datatype TreeTraversal<T> = InorderTraversal(Tree<T>) /* | PreorderTraversal(Tree<T>) | PostorderTraversal(Tree<T>) */ {
    method Enumerator() returns (e: Enumerator<T>) 
      ensures e.Valid()
      ensures fresh(e.Repr)
      ensures e.enumerated == []
    {
      match this
      case InorderTraversal(tree) => {
        e := InorderEnumerator(tree);
      }
    }
  }

  method InorderEnumerator<T>(tree: Tree<T>) returns (e: Enumerator<T>) 
    ensures e.Valid()
    ensures fresh(e.Repr)
    ensures e.enumerated == []
  {
    match tree
    case Nil => {
      e := new SeqEnumerator([]);
    }
    case Node(left, value, right) => {
      // TODO: How to make this lazy?
      var thisValueEnum := new SeqEnumerator([value]);
      var leftEnum := InorderEnumerator(left);
      var rightEnum := InorderEnumerator(right);
      var tmp := new ConcatEnumerator(leftEnum, thisValueEnum);
      e := new ConcatEnumerator(tmp, rightEnum);
    }
  }

  method Main() {
    var tree := Node(
      Node(
        Nil, 
        1, 
        Node(Nil, 2, Nil)
      ), 
      3,
      Node(
        Node(Nil, 4, Nil),
        5,
        Nil
      )
    );

    var traversal := InorderTraversal(tree);
    var e := traversal.Enumerator();
    while e.HasNext()
      invariant e.Valid() && fresh(e.Repr)
      decreases e.Decreases()
    {
      var x := e.Next();

      print x;
    }

    // With foreach loop support, the above could just be:
    //
    // foreach x in InorderTraversal(tree) {
    //   print x; 
    // }

  }
}