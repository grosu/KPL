/* Author: Grigore Rosu
   Date 26 January 2019
*/

module ERC20
  syntax Value   ::= Int  // this can be changed
  syntax Address ::= Int  // this can be changed
  syntax AExp ::= Value | Address
                | "totalSupply" "(" ")"
                | "balanceOf" "(" AExp ")"                       [strict]
                | "allowance" "(" AExp "," AExp ")"              [strict]
  syntax BExp ::= Bool
                | "approve" "(" AExp "," AExp ")"                [strict]
                | "transfer" "(" AExp "," AExp ")"               [strict]
                | "transferFrom" "(" AExp "," AExp "," AExp ")"  [strict]
                | "throw"
  syntax Event ::= "Transfer" "(" Address "," Address "," Value ")"
                 | "Approval" "(" Address "," Address "," Value ")"
  syntax EventLog ::= "Events:"
                    | EventLog Event

  configuration <ERC20>
                  <caller> 0 </caller>
                  <k> $PGM:K </k>
                  <accounts>
                    <account multiplicity="*">
                      <id> 0 </id>
                      <balance> 0 </balance>
                    </account>
                  </accounts>
                  <allowances>
                    <allowance multiplicity="*">
                      <owner> 0 </owner>
                      <spenders>
                        <allow multiplicity="*">
                          <spender> 0 </spender>
                          <amount> 0 </amount>
                        </allow>
                      </spenders>
                    </allowance>
                  </allowances>
                  <log> Events: </log>
                  <supply> 0 </supply>
                </ERC20>

  context <k> HOLE ...</k>
  context <log>... HOLE </log>

  syntax Int ::= "MAXVALUE"
  rule MAXVALUE = 2^256 - 1

  rule totalSupply() => Total ... supply: Total
  rule balanceOf(Id) => Value ... id: Id ... balance: Value

  rule allowance(Owner, Spender) => Allowance
  ...  owner: Owner ... spender: Spender ... amount: Allowance

  rule approve(_, Allowance) => throw
  requires Allowance < 0

  rule approve(Spender, Allowance) => true
  ...  caller: Owner ... owner: Owner ... spender: Spender
  ...  amount: _ => Allowance ...
  ...  . => Approval(Owner, Spender, Allowance)
  requires Allowance >= 0

  rule transfer(To, Value) => true
  ...  <caller> From </caller>
  ...  <account>
  ...    <id> From </id>
  ...    <balance> BalanceFrom => BalanceFrom -Int Value </balance>
  ...  </account>
  ...  <account>
  ...    <id> To </id>
  ...    <balance> BalanceTo => BalanceTo +Int Value </balance>
  ...  </account>
  ...  Log => Log Transfer(From, To, Value)
  requires To =/= From    // sanity check
        /\ 0 <= Value <= BalanceFrom
        /\ BalanceTo + Value <= MAXVALUE

  rule <k> transfer(From, Value) => true ...</k>
       <caller> From </caller>
       <id> From </id>
       <balance> BalanceFrom </balance>
       <log> Log => Log Transfer(From, From, Value) </log>
    requires Value >=Int 0
     andBool Value <=Int BalanceFrom

  rule <k> transfer(To, Value) => throw ...</k>
       <caller> From </caller>
       <account>
         <id> From </id>
         <balance> BalanceFrom </balance>
       </account>
       <account>
         <id> To </id>
         <balance> BalanceTo </balance>
       </account>
    requires To =/=Int From   // sanity check
     andBool (Value <Int 0
      orBool Value >Int BalanceFrom
      orBool BalanceTo +Int Value >Int MAXVALUE)

  rule <k> transfer(From, Value) => throw ...</k>
       <caller> From </caller>
       <id> From </id>
       <balance> BalanceFrom </balance>
    requires Value <Int 0
      orBool Value >Int BalanceFrom

  rule <k> transferFrom(From, To, Value) => true ...</k>
       <caller> Caller </caller>
       <owner> From </owner>
       <spender> Caller </spender>
       <amount> Allowance => Allowance -Int Value </amount>
       <account>
         <id> From </id>
         <balance> BalanceFrom => BalanceFrom -Int Value </balance>
       </account>
       <account>
         <id> To </id>
         <balance> BalanceTo => BalanceTo +Int Value </balance>
       </account>
       <log> Log => Log Transfer(From, To, Value) </log>
    requires To =/=Int From    // sanity check
     andBool Value >=Int 0
     andBool Value <=Int BalanceFrom
     andBool Value <=Int Allowance   // `transfer` does not check allowance
     andBool BalanceTo +Int Value <=Int MAXVALUE

  rule <k> transferFrom(From, From, Value) => true ...</k>
       <caller> Caller </caller>
       <owner> From </owner>
       <spender> Caller </spender>
       <amount> Allowance => Allowance -Int Value </amount>
       <id> From </id>
       <balance> BalanceFrom </balance>
       <log> Log => Log Transfer(From, From, Value) </log>
    requires Value >=Int 0
     andBool Value <=Int BalanceFrom
     andBool Value <=Int Allowance   // `transfer` does not check allowance

  rule <k> transferFrom(From, To, Value) => throw ...</k>
       <caller> Caller </caller>
       <owner> From </owner>
       <spender> Caller </spender>
       <amount> Allowance </amount>
       <account>
         <id> From </id>
         <balance> BalanceFrom </balance>
       </account>
       <account>
         <id> To </id>
         <balance> BalanceTo </balance>
       </account>
    requires To =/=Int From    // sanity check
     andBool (Value <Int 0
      orBool Value >Int BalanceFrom
      orBool Value >Int Allowance
      orBool BalanceTo +Int Value >Int MAXVALUE)

  rule <k> transferFrom(From, From, Value) => throw ...</k>
       <caller> Caller </caller>
       <owner> From </owner>
       <spender> Caller </spender>
       <amount> Allowance </amount>
       <id> From </id>
       <balance> BalanceFrom </balance>
    requires Value <Int 0
      orBool Value >Int BalanceFrom
      orBool Value >Int Allowance   // `transfer` does not check allowance

endmodule
