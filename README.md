Uma biblioteca da lógica de inconsistência formal LFI1 implementada em Rocq.

## Como compilar os arquivos:
- Ter o rocqide instalado
- No arquivo _CoqProject, consta:
  ```
  -R . [NomeDoProjeto]
  ./[NomeDoArquivo].v
  ```

- execute o comando rocq makefile -f _CoqProject -o CoqMakefile
- compile com make -f CoqMakefile
- depois, podemos limpar com make -f CoqMakefile clean
