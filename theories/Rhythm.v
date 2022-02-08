Inductive division : Type :=
    | whole
    | half : division -> division
    | third : division -> division
  .

  Inductive duration : Type :=
    | simple_duration : division -> duration
    | complex_duration : duration -> duration -> duration.

  Definition quarter := half(half(whole)).
  Eval compute in complex_duration (simple_duration quarter) (simple_duration quarter).
