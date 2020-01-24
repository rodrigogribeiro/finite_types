Require Export
        Omega
        Tactics.Crush
        Tactics.LibTactics.

Ltac matcher :=
  match goal with
  | [ H : context[if ?E then _ else _] |- _] =>
    let X := fresh "X" in destruct E eqn : X
  | [ H : context[ match ?E with _ => _ end ] |- _] =>
    let X := fresh "X" in destruct E eqn : X
  end.
