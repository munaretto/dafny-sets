/**
* Integrantes: Guilherme de Oliveira Munaretto e Luiz Pedro Franciscatto Guerra
*/

class {:autocontracts} Conjunto
{
    ghost var elementos: array<int>;
    var tamanho: int;

    // invariante de classe
    predicate Valid()
    reads this
    {
        tamanho >= 0 && elementos.Length >= 0
    }

    constructor()
    ensures Valid()
    {
        tamanho := 0;
        elementos := []; // ajustar construtor
    }

    // Adiciona um novo elemento no conjunto
    method Adicionar(elemento: int, c: Conjunto) returns (r: bool)
    requires Valid()
    ensures Valid()
    {}

    // Remove um elemento do conjunto
    method Remover(elemento: int, c: Conjunto) returns (r: bool)
    requires Valid()
    ensures Valid()
    {}

    // Verifica se o elemento pertence ao conjunto
    method Pertence(elemento: int, c: Conjunto) returns (r: bool)
    requires Valid()
    ensures Valid()
    {}

    // Retorna o número de elementos do conjunto
    method Tamanho(c: Conjunto) returns (r: int)
    requires Valid()
    ensures Valid()
    {
        r := tamanho;
    }

    // Verifica se o conjunto é vazio
    method Vazio(c: Conjunto) returns (r: bool)
    requires Valid()
    ensures Valid()
    {}

    // Realiza a união de dois conjuntos, retornando o conjunto resultante sem alterar os dois originais
    method Uniao(c1: Conjunto, c2: Conjunto) returns (c3: Conjunto)
    requires Valid()
    ensures Valid()
    {}

    // Realiza a intersecção de dois conjuntos, retornando o conjunto resultante sem alterar os dois originais
    method Interseccao(c1: Conjunto, c2: Conjunto) returns (c3: Conjunto)
    requires Valid()
    ensures Valid()
    {}

    // Realiza a diferença entre dois conjuntos, retornando o conjunto resultante sem alterar os dois originais
    method Diferenca(c1: Conjunto, c2: Conjunto) returns (c3: Conjunto)
    requires Valid()
    ensures Valid()
    {}

    // Método para testar funcionalidades da classe
    method Main()
    {}
}





