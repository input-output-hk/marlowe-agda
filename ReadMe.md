# An Agda Implementation of Marlowe Semantics

This repository implements [Marlowe Semantics](https://github.com/input-output-hk/marlowe/) in Agda. It is currently ***an experimental work in progress***.


## Development

Run `nix develop` to enter a Nix shell for the Agda environment. If the Agda environment has not been used previously, run `agda-mode setup && agda-mode compile`. Use `emacs` to edit `.agda` files.



## Example

The program [`main`](src/main.agda) creates and executes Marlowe's example *Escrow* contract. First, compile the program:

```bash
agda --compile src/main.agda
```

Then run it:

```bash
./src/main | json2yaml
```
```YAML
contract:
  timeout: 10
  timeout_continuation: close
  when:
  - case:
      deposits: 1000
      into_account:
        role_token: Seller
      of_token:
        currency_symbol: ''
        token_name: ''
      party:
        role_token: Buyer
    then:
      timeout: 20
      timeout_continuation: close
      when:
      - case:
          choose_between:
          - from: 0
            to: 0
          for_choice:
            choice_name: Everything is alright
            choice_owner:
              role_token: Buyer
        then: close
      - case:
          choose_between:
          - from: 1
            to: 1
          for_choice:
            choice_name: Report problem
            choice_owner:
              role_token: Buyer
        then:
          from_account:
            role_token: Seller
          pay: 1000
          then:
            timeout: 30
            timeout_continuation: close
            when:
            - case:
                choose_between:
                - from: 1
                  to: 1
                for_choice:
                  choice_name: Confirm problem
                  choice_owner:
                    role_token: Seller
              then: close
            - case:
                choose_between:
                - from: 0
                  to: 0
                for_choice:
                  choice_name: Dispute problem
                  choice_owner:
                    role_token: Seller
              then:
                timeout: 40
                timeout_continuation: close
                when:
                - case:
                    choose_between:
                    - from: 0
                      to: 0
                    for_choice:
                      choice_name: Dismiss claim
                      choice_owner:
                        role_token: Mediator
                  then:
                    from_account:
                      role_token: Buyer
                    pay: 1000
                    then: close
                    to:
                      account:
                        role_token: Seller
                    token:
                      currency_symbol: ''
                      token_name: ''
                - case:
                    choose_between:
                    - from: 1
                      to: 1
                    for_choice:
                      choice_name: Confirm claim
                      choice_owner:
                        role_token: Mediator
                  then: close
          to:
            account:
              role_token: Buyer
          token:
            currency_symbol: ''
            token_name: ''
inputs:
- tx_inputs:
  - input_from_party:
      role_token: Buyer
    into_account:
      role_token: Seller
    of_token:
      currency_symbol: ''
      token_name: ''
    that_deposits: 1000
  tx_interval:
    from: 0
    to: 5
- tx_inputs:
  - for_choice_id:
      choice_name: Everything is alright
      choice_owner:
        role_token: Buyer
    input_that_chooses_num: 0
  tx_interval:
    from: 0
    to: 5
minTime: 0
output:
  contract: close
  payments:
  - amount: 1000
    payment_from:
      role_token: Seller
    to:
      party:
        role_token: Seller
    token:
      currency_symbol: ''
      token_name: ''
  state:
    accounts: []
    boundValues: []
    choices:
    - - choice_name: Everything is alright
        choice_owner:
          role_token: Buyer
      - 0
    minTime: 0
  warnings: []
```
