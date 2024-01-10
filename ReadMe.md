# An implementation of Marlowe semantics in Agda

This repository implements [Marlowe Semantics](https://github.com/input-output-hk/marlowe/) in Agda. It is currently ***an experimental work in progress***.

## Development

Run `nix develop` to enter a Nix shell for the Agda environment. If the Agda environment has not been used previously, run `agda-mode setup && agda-mode compile`. Use `emacs` to edit `.agda`, `.lagda` and `.lagda.md` files.

## Example

The program [`main`](src/main.lagda.md) creates and executes Marlowe's example *Escrow* contract. First, compile the program:

```bash
cabal build lib:marlowe-agda
cabal run marlowe-agda
```

Outputs the initial contract

```
When
    [Case
        (Deposit
            (Role "Seller")
            (Role "Buyer")
            (Token "" "")
            (Constant 1000)
        )
        (When
            [Case
                (Choice
                    (ChoiceId
                        "Everything is alright"
                        (Role "Buyer")
                    )
                    [Bound 0 0]
                )
                Close , Case
                (Choice
                    (ChoiceId
                        "Report problem"
                        (Role "Buyer")
                    )
                    [Bound 1 1]
                )
                (Pay
                    (Role "Seller")
                    (Account (Role "Buyer"))
                    (Token "" "")
                    (Constant 1000)
                    (When
                        [Case
                            (Choice
                                (ChoiceId
                                    "Confirm problem"
                                    (Role "Seller")
                                )
                                [Bound 1 1]
                            )
                            Close , Case
                            (Choice
                                (ChoiceId
                                    "Dispute problem"
                                    (Role "Seller")
                                )
                                [Bound 0 0]
                            )
                            (When
                                [Case
                                    (Choice
                                        (ChoiceId
                                            "Dismiss claim"
                                            (Role "Mediator")
                                        )
                                        [Bound 0 0]
                                    )
                                    (Pay
                                        (Role "Buyer")
                                        (Account (Role "Seller"))
                                        (Token "" "")
                                        (Constant 1000)
                                        Close
                                    ), Case
                                    (Choice
                                        (ChoiceId
                                            "Confirm claim"
                                            (Role "Mediator")
                                        )
                                        [Bound 1 1]
                                    )
                                    Close ]
                                40 Close
                            )]
                        30 Close
                    )
                )]
            20 Close
        )]
    10 Close
```

and the payment

```
Payment (AccountId (Role "Seller")) (Token "" "") 1000 (Party (Role "Seller"))
```
