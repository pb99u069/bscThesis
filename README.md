# 2021.bsc.peter.bruehwiler

execute perdex (cabal run uniswap-pab, cabal run uniswap-client -- walletnr.) inside a nix-shell. the nix build file (shell.nix) is in the [plutus](https://github.com/input-output-hk/plutus) repository. for the dependencies to work, before entering the nix-shell from the plutus repo checkout the repo at commit 7b5829f2ac57fcfa25a5969ff602b48641b36ac3 (as stated in the cabal.project file inside the perdex repo)
