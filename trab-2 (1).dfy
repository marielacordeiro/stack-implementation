/*
  Class Stack.

  Nomes:
  Mariela Pontes Cordeiro,
  Maria Eduarda Menezes de Lemos,
  Bruno Brandão,
  Gustavo Fernando Burchardt,
  Eduardo Ribeiro Barcellos
*/

class {:autocontracts}  Stack
{
    // variáveis de implementação
    var arr: array<int> // array de inteiros concreto
    var capacity: nat
    var size: nat // índice da próxima posição livre e quantidade de elementos na pilha

    // representação abstrata
    ghost var elements: seq<int> // array abstrato 
    ghost var arrCapacity: nat // capacidade abstrata


    ghost predicate Valid()
    {
        // define invariante da classe - condições que devem sempre ser verdadeiras
        capacity > 0
        && 0 <= size <= capacity 
        && arrCapacity == capacity
        && arr.Length == capacity
        && elements == arr[0..size]
    }

    constructor()
    ensures elements == []
    ensures size == 0
    {
        // construtor deve instanciar uma pilha vazia
        capacity := 8;
        size := 0;
        arr := new int[8];
        
        elements := [];
        arrCapacity := capacity;
    }

    // adiciona um novo elemento na pilha
    method Push(e:int)
    ensures size == old(size) + 1
    ensures elements == old(elements) + [e]
    {
        // verifica se a pilha está cheia, se estiver, aumenta capacidade copiando os dados para uma nova pilha
        if IsFull()
        {
            var newCapacity :=  capacity * 2;
            var newArr := new int[newCapacity];

            forall i | 0 <= i < size
            {
                newArr[i] := arr[i];
            }

            arr := newArr;
            capacity := newCapacity;
            arrCapacity := capacity;
            elements := arr[..size];
        }
        
        arr[size] := e; // adiciona elemento na proxima posição livre da pilha
        size := size + 1;
        elements := elements + [e];
    }

    // remove um elemento da pilha, caso ela não esteja vazia
    method Pop()
    requires !IsEmpty()
    ensures size == old(size) - 1
    ensures elements == old(elements)[0..|old(elements)| - 1]
    {
        size := size - 1;
        elements := arr[..size];
    }

    // le o valor do topo da pilha, sem removê-lo
    method Peek() returns (elem : int)
    requires !IsEmpty()
    ensures elements == old(elements)
    ensures elem == elements[|elements| - 1]
    {
        elem := arr[size-1];
    }

    // verifica se a pilha está vazia ou não
    predicate IsEmpty()
    ensures IsEmpty() <==> (|elements| == 0)
    {
        size == 0
    }

    // verifica se a pilha está cheia
    predicate IsFull()
    ensures IsFull() <==> |elements| == capacity
    {
        size == arr.Length
    }

    // informa o número de elementos armazenados na pilha
    function Size(): nat
    ensures Size() == |elements|
    {
        size
    }

    // inverte a ordem dos elementos da pilha
    method Invert()
    ensures |elements| == |old(elements)|
    ensures forall i | 0 <= i < |elements| :: elements[i] == old(elements[|elements| - i - 1])
    {
        var a := new int[capacity];

        forall i | 0 <= i < size
        {
            a[i] := arr[size - i - 1];
        }

        arr := a;
        elements := arr[..size];
    }

    // empilha uma pilha sobre outra, retornando uma nova pilha
    method Concatenate(other: Stack) returns(result: Stack)
    requires Valid() && other.Valid()
    requires other != this
    ensures fresh(result)
    ensures result.elements == elements + other.elements
    ensures elements == old(elements)
    ensures other.elements == old(other.elements)
    {
        result := new Stack();
        
        // calcula nova capacidade
        var newCapacity := capacity + other.capacity;
        result.capacity := newCapacity;
        result.arr := new int[newCapacity];
        result.size := size + other.size;
        
        // copia primeira pilha
        forall i | 0 <= i < size {
            result.arr[i] := arr[i];
        }
        
        // copia segunda pilha  
        forall i | 0 <= i < other.size {
            result.arr[size + i] := other.arr[i];
        }
        
        result.elements := elements + other.elements;
        result.arrCapacity := newCapacity;
    }
}

method Main()
{
    TestEmptyStack();
    TestPushAndPeek();
    TestPop();
    TestInvert();
    TestConcatenate();
    TestUnlimitedSize();
}

method TestEmptyStack()
{
    var stack := new Stack();

    assert stack.IsEmpty() == true;
    assert stack.Size() == 0;
}

method TestPushAndPeek()
{
    var stack := new Stack();
    stack.Push(42);
    var elem := stack.Peek();

    assert elem == 42;
}

method TestPop()
{
    var stack := new Stack();
    stack.Push(99);
    stack.Pop();
    assert stack.IsEmpty() == true;
}

method TestInvert()
{
    var stack := new Stack();
    stack.Push(1);
    stack.Push(2);
    stack.Push(3);

    stack.Invert();

    assert stack.elements == [3, 2, 1];
}

method TestConcatenate()
{
    var s1 := new Stack();
    s1.Push(1);
    s1.Push(3);

    var s2 := new Stack();
    s2.Push(5);
    s2.Push(6);
    s2.Push(7);

    var res := s1.Concatenate(s2);

    assert res.elements == [1, 3, 5, 6, 7];
    assert s1.elements == [1, 3];
    assert s2.elements == [5, 6, 7];
}

method TestUnlimitedSize()
{
    var stack := new Stack();

    stack.Push(0);
    stack.Push(1);
    stack.Push(2);
    stack.Push(3);
    stack.Push(4);
    stack.Push(5);
    stack.Push(6);
    stack.Push(7);
    stack.Push(8);
    stack.Push(9);
    stack.Push(10);
    stack.Push(11);
    stack.Push(12);

    assert stack.Size() == 13;

    stack.Pop(); 
    stack.Pop(); 
    stack.Pop(); 
    stack.Pop();
    stack.Pop();
    stack.Pop();
    stack.Pop();
    stack.Pop();
    stack.Pop();
    stack.Pop();
    stack.Pop();
    stack.Pop();
    stack.Pop();

    assert stack.IsEmpty() == true;
}