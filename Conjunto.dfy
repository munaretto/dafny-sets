/**
* Integrantes: Guilherme de Oliveira Munaretto e Luiz Pedro Franciscatto Guerra
*/

class {:autocontracts} Conjunto
{
    var arr: array<int>;
    var elemCount: int;
    var size: int;

    ghost var elements: seq<int>;

    // invariante de classe
    predicate Valid()
    reads this
    {
        0 <= elemCount <= arr.Length &&
        elements == arr[0..elemCount - 1] && // verificar limites
        size >= 10 && 
        size <= arr.Length
        // verificar se existe elementos repetidos
    }

    predicate method isEmpty()
    requires Valid()
    {
        elemCount == 0
    }

    predicate Empty()
    requires Valid()
    {
        elemCount == 0
    }

    constructor() // verificar pos condição
    ensures Valid()
    ensures Empty()
    {
        elemCount := 0; // configura o contador de elementos existentes
        size := 10; // configura tamanho inicial pra estrutura de dados
        arr := new int[10]; // cria um novo array com o tamanho estipulado
    }

    // 1 - Adiciona um novo elemento no conjunto
    method Adicionar(elemento: int) returns (r: bool)
    requires Valid()
    ensures Valid()
    {}

    // 2 - Remove um elemento do conjunto
    method Remover(elemento: int) returns (r: bool)
    requires Valid()
    ensures Valid()
    {}

    // 3 - Verifica se o elemento pertence ao conjunto
    method Pertence(elemento: int) returns (r: bool)
    requires Valid()
    ensures Valid()
    {}

    // 4 - Retorna o número de elementos do conjunto
    method Tamanho() returns (r: int)
    requires Valid()
    ensures Valid() 
    ensures r == elemCount
    {
        r := elemCount;
    }

    // 5 - Verifica se o conjunto é vazio
    method Vazio() returns (r: bool)
    requires Valid()
    ensures Valid()
    {
        r := isEmpty();
    }

    // 6 - Realiza a união de dois conjuntos, retornando o conjunto resultante sem alterar os dois originais
    method Uniao(c1: Conjunto, c2: Conjunto) returns (c3: Conjunto)
    requires Valid()
    ensures Valid()
    {}

    // 7 - Realiza a intersecção de dois conjuntos, retornando o conjunto resultante sem alterar os dois originais
    method Interseccao(c1: Conjunto, c2: Conjunto) returns (c3: Conjunto)
    requires Valid()
    ensures Valid()
    {}

    // 8 - Realiza a diferença entre dois conjuntos, retornando o conjunto resultante sem alterar os dois originais
    method Diferenca(c1: Conjunto, c2: Conjunto) returns (c3: Conjunto)
    requires Valid()
    ensures Valid()
    {}

    
}

// Método para testar funcionalidades da classe
method Main()
{}




