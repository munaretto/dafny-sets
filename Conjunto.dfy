/**
* Integrantes: Guilherme de Oliveira Munaretto, Luiz Pedro Franciscatto Guerra, Marcelo Kohut e Wagner Santos 
*/

class {:autocontracts} Conjunto
{
    //Implementação
    var content: array<int>;
    var count: nat;

    //Abstração (ghost)
    ghost var g_content: seq<int>;

    predicate Valid()
    {
        content.Length != 0
        && 0 <= count <= content.Length
        && content[0..count] == g_content
        && forall i,j :: 0 <= i < count // garante que nao existe elementos duplicados
        && 0 <= j < count
        && i != j ==> content[i] != content[j]
    }

    // Construtor deve instanciar um conjunto vazio.
    constructor ()
    ensures g_content == []
    {
        content := new int[5];
        count := 0;
        g_content := [];
    }
    
    // Adicionar  um  novo  elemento  no conjunto  e  retornar  verdadeiro caso  adicionardo, 
    // e retornar falso caso o elemento já se encontre no conjunto.
    method Adicionar(element:int) returns (success:bool)
    requires count <= content.Length;
    ensures element in old(g_content) ==> |g_content| == |old(g_content)|;
    ensures !(element in old(g_content)) ==> count == old(count) + 1;
    ensures element in old(g_content) ==> (g_content == old(g_content)) && success == false;
    ensures !(element in old(g_content)) ==> (g_content == old(g_content) + [element]) && success == true;
    {
        var verify := Pertence(element);
        if(!verify) {
            if(count == content.Length) {
                var newSize := new int[2 * content.Length];
                var i := 0;
                forall(i | 0 <= i <= count-1) {
                    newSize[i] := content[i];
                }
                content := newSize;
            }
            content[count] := element;
            count := count + 1;
            g_content := g_content + [element];
            success := !verify;
        } else {
            success := !verify;
        }
    }

    // Remover um elemento do conjunto e retornar verdadeiro caso removido, 
    // e retornar falso caso o elemento não se encontrava no conjunto.
    method Remover(element:int) returns (success:bool)
    requires count <= content.Length;
    {
        var contains := Pertence(element);
        if (contains) {
            success := true;
        }
        else {
            success := false;
        }
    }

    // Verificar se um determinado elemento pertence o não a um conjunto.
    method Pertence(element:int) returns (success:bool)
    requires count <= content.Length;
    ensures success <==> element in g_content;
    {
        success := false;
        var i := 0;
        while (i < count)
        invariant 0 <= i <= count
        invariant (i > 0) ==> success == (element in g_content[0..i])
        invariant (i == 0) ==> !success
        decreases count - i {
            if(content[i] == element) {
                success := true;
            }
            i := i + 1;
        }
        return success;
    }


    // Retornar o número de elementos do conjunto.
    method Tamanho() returns (total:int)
    requires count >= 0;
    ensures total == |g_content|;
    {
        return count;
    }
    
    // Verificar se um conjunto é vazio ou não.
    method Vazio() returns (success:bool)
    requires count == 0;
    ensures g_content == [];
    {
        return count == 0;
    }

    // Realizar a união de dois conjuntos retornando um novo conjunto como resultado, sem alterar os conjuntos originais.
    method Uniao(inputSet:Conjunto) returns (newSet:Conjunto)
    requires |g_content| >= 0;
    requires |inputSet.g_content| >= 0;
    ensures |newSet.g_content| >= 0;
    ensures forall i :: (0 <= i < |g_content|) ==> g_content[i] in newSet.g_content;
    ensures forall i :: (0 <= i < |inputSet.g_content|) ==> inputSet.g_content[i] in newSet.g_content;
    ensures |newSet.g_content| <= |g_content| + |inputSet.g_content|;
    {
        // Declaracao do novo conjunto e suas variaveis
        newSet := new Conjunto();
        newSet.count := count + inputSet.count;
        newSet.content := new int[count + inputSet.count];
        newSet.g_content := [];

        var i := 0;
        var j := 0;
        while(i < count)
        decreases count - i;
        invariant 0 <= i <= count;
        {
            var b := newSet.Adicionar(content[i]);
            i := i + 1;
        }

        while(j < inputSet.count)
        decreases inputSet.count - j;
        invariant 0 <= j <= inputSet.count;
        {
            var verify := Pertence(inputSet.content[count+j]);
            if(!verify){
                var b := newSet.Adicionar(inputSet.content[count+j]);
            }
            j := j + 1;
        }
        newSet.count := i+j;
        return newSet;
    }
    
    // Realizar a intersecção de dois conjuntos retornandoum novo conjunto como resultado, sem alterar os conjuntos originais.
    method Interseccao(inputSet:Conjunto) returns (newSet:Conjunto)
    requires |g_content| >= 0
    requires |inputSet.g_content| >= 0
    ensures |newSet.g_content| >= 0
    ensures forall i:: (0 <= i< |newSet.g_content|) ==> newSet.g_content[i] in g_content
    ensures forall i:: (0 <= i< |newSet.g_content|) ==> newSet.g_content[i] in inputSet.g_content
    ensures forall i,j :: (0 <= i < |newSet.g_content|)
                        && (0 <= j < |newSet.g_content|)
                        && (i != j) ==> newSet.g_content[i]
                        != newSet.g_content[j]
    {
        newSet := new Conjunto();
        newSet.count := count + inputSet.count;
        newSet.content := new int[count + inputSet.count];
        newSet.g_content := [];

        var i := 0;
        while(i < count)
        decreases count - i
        invariant 0 <= i <= count
        {
            var verify := inputSet.Pertence(content[i]);
            if(verify)
            {
                var b := newSet.Adicionar(content[i]);
            }
            i := i + 1;
        }
        return newSet;
    }

    
    // Realizar a diferença de dois conjuntos retornandoum novo conjunto  como  resultado, sem alterar os conjuntos originais
    method Diferenca(inputSet:Conjunto) returns (newSet:Conjunto)
    requires |g_content| >= 0
    requires |inputSet.g_content| >= 0
    ensures |newSet.g_content| >= 0
    ensures forall i :: (0 <= i < |newSet.g_content|) ==> ((newSet.g_content[i] in g_content) && !(newSet.g_content[i] in inputSet.g_content))
                    || (newSet.g_content[i] in inputSet.g_content && !(newSet.g_content[i] in g_content))
    {
        // Declaracao do novo conjunto
        newSet := new Conjunto();
        newSet.count := count + inputSet.count;
        newSet.content := new int[count + inputSet.count];
        newSet.g_content := [];

        var i := 0;
        var k := 0;
        while(i < count)
        decreases count - i
        invariant 0 <= i <= count
        {
            var verify := Pertence(content[i]);
            if(!verify){
                var b := newSet.Adicionar(content[i]);
            }
            i := i + 1;
        }

        while(k < inputSet.count)
        decreases inputSet.count - k
        invariant 0 <= k <= inputSet.count
        {
            var verify := Pertence(inputSet.content[k]);
            if(!verify){
                var b := newSet.Adicionar(inputSet.content[k]);
            }
            k := k + 1;
        }
        return newSet;
    }
}

method Main()
{
    // ADICIONAR - Testa a adicao de valores
    var firstSet := new Conjunto();
    assert firstSet.g_content == [];
    var b := firstSet.Adicionar(1);
    assert firstSet.g_content == [1];
    b := firstSet.Adicionar(2);
    assert b ==  true;
    b := firstSet.Adicionar(3);
    assert b ==  true;
    b := firstSet.Adicionar(4);
    assert b ==  true;
    b := firstSet.Adicionar(4);
    assert b == false;

    // PERTENCE - Verificacao se Pertence ou nao
    b := firstSet.Adicionar(5);
    b := firstSet.Pertence(5);
    assert b == true;

    b := firstSet.Pertence(6);
    assert b == false;

    // TAMANHO - Verifica numero de elementos no conjunto
    var returnedSize := firstSet.Tamanho();
    assert returnedSize == 5;
    assert |firstSet.g_content| == 5;

    // REMOVER - Testa remoção de elemento de um conjunto
    var testSet := new Conjunto();
    var elem := testSet.Adicionar(2);
    assert |testSet.g_content| == 1;
    var canRemove := testSet.Remover(2);
    assert canRemove == true;
    assert |testSet.g_content| == 0;
    var canNotRemove := testSet.Remover(10);
    assert canNotRemove == false;

    // Testando operações sobre conjuntos
    var secondSet := new Conjunto();
    var c := secondSet.Adicionar(6);
    c := secondSet.Adicionar(7);
    c := secondSet.Adicionar(8);
    c := secondSet.Adicionar(9);
    
    // UNIAO
    var UniaoSet := firstSet.Uniao(secondSet);
    assert UniaoSet.count == 9;

    // INTERSECÇÃO
    var thirdSet := new Conjunto();
    var d := secondSet.Adicionar(1);
    d := secondSet.Adicionar(2);

    var InterseccaoSet := firstSet.Interseccao(thirdSet);
    assert InterseccaoSet.count == 2;

    // DIFERENÇA
    var fourthSet := new Conjunto();
    var e := secondSet.Adicionar(1);
    e := secondSet.Adicionar(2);

    var DiferencaSet := firstSet.Diferenca(fourthSet);
    assert DiferencaSet.count == 7;
}




