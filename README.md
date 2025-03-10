Uma biblioteca da lógica de inconsistência formal LFI1 implementada em Coq.

## Como compilar os arquivos:
- Ter o coqide instalado
- No arquivo _CoqProject, consta:
  ```
  -R . [NomeDoProjeto]
  ./[NomeDoArquivo].v
  ```

- execute o comando coq_makefile -f _CoqProject -o CoqMakeFile
- compile com make -f CoqMakeFile
- depois, podemos limpar com make -f CoqMakeFile clean
