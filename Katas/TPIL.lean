namespace Chapter3
  /- 1. Prove the following identities, replacing the sorry placeholders with actual proofs. -/
  variable (p q r : Prop)

  -- commutativity of ∧ and ∨
  example : p ∧ q ↔ q ∧ p :=
    Iff.intro
      (fun (pq : p ∧ q) => And.intro (And.right pq) (And.left pq))
      (fun (qp : q ∧ p) => And.intro (And.right qp) (And.left qp))

  example : p ∨ q ↔ q ∨ p :=
    Iff.intro
      (fun (pq : p ∨ q) =>
        Or.elim pq
          (fun (p : p) => Or.inr p)
          (fun (q : q) => Or.inl q))
      (fun (qp : q ∨ p) =>
        Or.elim qp
          (fun (q : q) => Or.inr q)
          (fun (p : p) => Or.inl p))

  -- associativity of ∧ and ∨
  example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
    Iff.intro
      (And.elim (fun (pq : p ∧ q) (r : r) =>
        pq |> And.elim (fun (p : p) (q : q) =>
          And.intro p (And.intro q r))))
      (And.elim (fun (p : p) (qr : q ∧ r) =>
        qr |> And.elim (fun (q : q) (r : r) =>
          And.intro (And.intro p q) r)))

  example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
    Iff.intro
      (fun (pqr : (p ∨ q) ∨ r) =>
        Or.elim pqr
          (fun (pq : p ∨ q) =>
            Or.elim pq
              (fun (p : p) => Or.inl p)
              (fun (q : q) => Or.inr (Or.inl q)))
          (fun (r : r) =>
            Or.inr (Or.inr r)))
      (fun (pqr : p ∨ (q ∨ r)) =>
        Or.elim pqr
          (fun (p : p) => Or.inl (Or.inl p))
          (fun (qr : q ∨ r) =>
            Or.elim qr
              (fun (q : q) => Or.inl (Or.inr q))
              (fun (r : r) => Or.inr r)))

  -- distributivity
  example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
    Iff.intro
      (fun (pqr : p ∧ (q ∨ r)) =>
        And.elim (fun (p : p) (qr : q ∨ r) =>
          Or.elim qr
            (fun (q : q) => Or.inl (And.intro p q))
            (fun (r : r) => Or.inr (And.intro p r)))
          pqr)
      (fun (pqpr : (p ∧ q) ∨ (p ∧ r)) =>
        Or.elim pqpr
          (fun (pq : p ∧ q) =>
            And.elim
              (fun (p : p) (q : q) => And.intro p (Or.inl q))
              pq)
          (fun (pr : p ∧ r) =>
            And.elim
              (fun (p : p) (r : r) => And.intro p (Or.inr r))
              pr))

  example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
    Iff.intro
      (fun (pqr : p ∨ (q ∧ r)) =>
        Or.elim pqr
          (fun (p : p) => And.intro (Or.inl p) (Or.inl p))
          (fun (qr : q ∧ r) =>
            And.elim
              (fun (q : q) (r : r) => And.intro (Or.inr q) (Or.inr r))
              qr))
      (fun (pqpr : (p ∨ q) ∧ (p ∨ r)) =>
        And.elim (fun (pq : p ∨ q) (pr : p ∨ r) =>
          Or.elim pq
            (fun p : p => Or.inl p)
            (fun q : q =>
              Or.elim pr
                (fun p : p => Or.inl p)
                (fun r : r => Or.inr (And.intro q r)))
        ) pqpr)

  -- other properties
  example : (p → (q → r)) ↔ (p ∧ q → r) :=
    Iff.intro
      (fun pqr : (p → (q → r)) =>
        (fun (pq : p ∧ q) =>
          And.elim
            (fun (p : p) (q : q) => (pqr p) q) pq))
      (fun pqr : (p ∧ q → r) =>
        (fun p : p =>
          (fun q : q =>
            pqr (And.intro p q))))

  example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
    Iff.intro
      (fun pqr : (p ∨ q) → r =>
        And.intro
          (fun p : p => pqr (Or.inl p))
          (fun q : q => pqr (Or.inr q))
      )
      (fun prqr : (p → r) ∧ (q → r) =>
        And.elim (fun (pr : p → r) (qr : q → r) =>
          (fun pq : p ∨ q =>
            Or.elim pq
              (fun p : p => pr p)
              (fun q : q => qr q)
          )
        ) prqr
      )

  example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
    Iff.intro
      (fun npq : ¬(p ∨ q)=>
        And.intro
          (fun p : p => npq (Or.inl p))
          (fun q : q => npq (Or.inr q)))
      (fun npnq : ¬p ∧ ¬q =>
        And.elim
          (fun (np : ¬p) (nq : ¬q) =>
            fun (pq : p ∨ q) =>
              Or.elim pq
                (fun p : p => np p)
                (fun q : q => nq q))
          npnq)

  example : ¬p ∨ ¬q → ¬(p ∧ q) :=
    (fun npnq : ¬p ∨ ¬q =>
      Or.elim npnq
        (fun np : ¬p =>
          (fun pq : p ∧ q => np (And.left pq)))
        (fun nq : ¬q =>
          (fun pq : p ∧ q => nq (And.right pq))))

  example : ¬(p ∧ ¬p) :=
    (fun pnp : p ∧ ¬p =>
      And.elim (fun (hp : p) (np : ¬p) => np hp) pnp)

  example : p ∧ ¬q → ¬(p → q) :=
    (fun hpnq : p ∧ ¬q =>
      And.elim
        (fun (hp : p) (hnq : ¬q) =>
          (fun hpq : p → q => hnq (hpq hp)))
        hpnq)

  example : ¬p → (p → q) :=
    (fun hnp : ¬p =>
      (fun hp : p =>
        absurd hp hnp
      )
    )

  example : (¬p ∨ q) → (p → q) :=
    (fun hnpq : ¬p ∨ q =>
      Or.elim hnpq
        (fun hnp : ¬p =>
          (fun hp : p =>
            absurd hp hnp
          )
        )
        (fun hq : q =>
          (fun _ : p => hq)
        )
    )

  example : p ∨ False ↔ p :=
    Iff.intro
      (fun hpF : p ∨ False =>
        Or.elim hpF
          (fun hp : p => hp)
          False.elim)
      (fun hp : p => Or.inl hp)

  example : p ∧ False ↔ False :=
    Iff.intro And.right False.elim

  example : (p → q) → (¬q → ¬p) :=
    (fun hpq : p → q =>
      (fun (hnq : ¬q) =>
        (fun hp : p =>
          hnq (hpq hp)
        )
      )
    )

  /- Prove the following identities, replacing the sorry placeholders with actual proofs. These require classical reasoning. -/

  namespace WithClassical
    open Classical

    variable (p q r : Prop)

    example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
      (fun hpqr : p → q ∨ r =>
        Or.elim (em p)
          (fun hp : p =>
            Or.elim (hpqr hp)
              (fun hq : q => Or.inl (fun _ : p => hq))
              (fun hr : r => Or.inr (fun _ : p => hr))
          )
          (fun hnp : ¬p =>
            Or.inl (fun hp : p => absurd hp hnp))
      )
    example : ¬(p ∧ q) → ¬p ∨ ¬q :=
      (fun hnpq : ¬(p ∧ q) =>
        Or.elim (em p)
          (fun hp : p =>
            Or.elim (em q)
              (fun hq : q => absurd (And.intro hp hq) hnpq)
              (fun hnq : ¬q => Or.inr hnq))
          (fun hnp : ¬p =>
            Or.inl hnp)
      )

    example : ¬(p → q) → p ∧ ¬q :=
      (fun hnpq : ¬(p → q) =>
        Or.elim (em q)
          (fun hq : q => absurd (fun _ : p => hq) hnpq)
          (fun hnq : ¬q =>
            Or.elim (em p)
              (fun hp : p => And.intro hp hnq)
              (fun hnp : ¬p => absurd (fun hp : p => absurd hp hnp) hnpq)
          )
      )

    example : ¬(p → q) → p ∧ ¬q :=
      (fun hnpq : ¬(p → q) =>
        Or.elim (em p)
          (fun hp : p => And.intro hp (fun hq : q => hnpq (fun _ : p => hq)))
          (fun hnp : ¬p => absurd (fun hp : p => absurd hp hnp) hnpq))

    example : (p → q) → (¬p ∨ q) :=
      (fun hpq : p → q =>
        Or.elim (em p)
          (fun hp : p =>
            Or.elim (em q)
              (fun hq : q => Or.inr hq)
              (fun hnq : ¬q => absurd (hpq hp) hnq))
          (fun hnp : ¬p => Or.inl hnp)
      )

    example : (¬q → ¬p) → (p → q) :=
      (fun hnqnp : ¬q → ¬p =>
        Or.elim (em q)
          (fun hq : q => (fun _ : p => hq))
          (fun hnq : ¬q =>
            (fun hp : p =>
              absurd hp (hnqnp hnq)
            )
          )
      )

    example : p ∨ ¬p := em p

    example : (((p → q) → p) → p) :=
      (fun hf : (p → q) → p =>
        Or.elim (em p)
          (fun hp : p => hp)
          (fun hnp : ¬p => hf (fun hp : p => absurd hp hnp))
      )
  end WithClassical

  /- 3. Prove ¬(p ↔ ¬p) without using classical logic.  -/
  /- NOTE: This one is hard! -/
  example : ¬(p ↔ ¬p) :=
    (fun h : (p ↔ ¬p) =>
      Iff.elim
        (fun (hl : p → ¬p) (hr : ¬p → p) =>
          have np : ¬p := fun hp => hl hp hp
          np (hr np)
        ) h
    )
end Chapter3

namespace Chapter4
  /- 1. Prove these equivalences -/
  variable (α : Type) (p q : α → Prop)
  example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
    Iff.intro
      (fun h : ∀ x, p x ∧ q x =>
        And.intro
          (fun x : α => (h x).left)
          (fun x : α => (h x).right)
      )
      (fun h : (∀ x, p x) ∧ (∀ x, q x) =>
        (fun x : α =>
          And.intro (h.left x) (h.right x)
        )
      )

  example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
    (fun hxpq : ∀ x, p x → q x =>
      (fun hxp : ∀ x, p x =>
        (fun x : α =>
          (hxpq x) (hxp x)
        )
      )
    )

  example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
    (fun hxpxq : (∀ x, p x) ∨ (∀ x, q x) =>
      (fun x : α =>
        Or.elim hxpxq
          (fun hxp : ∀ x, p x => Or.inl (hxp x))
          (fun hxq : ∀ x, q x => Or.inr (hxq x))
      )
    )

  /- 2. It is often possible to bring a component of a formula outside a universal quantifier, when it does not depend on the quantified variable. Try proving these (one direction of the second of these requires classical logic): -/
  variable (α : Type) (p q : α → Prop)
  variable (r : Prop)

  example : α → ((∀ x : α, r) ↔ r) := sorry
  example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry
  example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := sorry

  /- 3. Consider the “barber paradox,” that is, the claim that in a certain town there is a (male) barber that shaves all and only the men who do not shave themselves. Prove that this is a contradiction: -/
  variable (men : Type) (barber : men)
  variable (shaves : men → men → Prop)

  example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := sorry

  /- 4. Remember that, without any parameters, an expression of type Prop is just an assertion. Fill in the definitions of prime and Fermat_prime below, and construct each of the given assertions. For example, you can say that there are infinitely many primes by asserting that for every natural number n, there is a prime number greater than n. Goldbach's weak conjecture states that every odd number greater than 5 is the sum of three primes. Look up the definition of a Fermat prime or any of the other statements, if necessary. -/
  def even (n : Nat) : Prop := sorry
  def prime (n : Nat) : Prop := sorry
  def infinitely_many_primes : Prop := sorry
  def Fermat_prime (n : Nat) : Prop := sorry
  def infinitely_many_Fermat_primes : Prop := sorry
  def goldbach_conjecture : Prop := sorry
  def Goldbach's_weak_conjecture : Prop := sorry
  def Fermat's_last_theorem : Prop := sorry

  /- 5. Prove as many of the identities listed in the Existential Quantifier section as you can. -/
  namespace WithClassical
    open Classical

    variable (α : Type) (p q : α → Prop)
    variable (r : Prop)

    example : (∃ x : α, r) → r := sorry
    example (a : α) : r → (∃ x : α, r) := sorry
    example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := sorry
    example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := sorry

    example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry
    example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
    example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
    example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

    example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
    example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
    example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
  end WithClassical
end Chapter4

namespace Chapter5

  namespace Chapter3WithTactics
    /- 1. Prove the following identities, replacing the sorry placeholders with actual proofs. -/

    variable (p q r : Prop)

    -- commutativity of ∧ and ∨
    example : p ∧ q ↔ q ∧ p := sorry
    example : p ∨ q ↔ q ∨ p := sorry

    -- associativity of ∧ and ∨
    example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := sorry
    example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

    -- distributivity
    example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
    example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

    -- other properties
    example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
    example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
    example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
    example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
    example : ¬(p ∧ ¬p) := sorry
    example : p ∧ ¬q → ¬(p → q) := sorry
    example : ¬p → (p → q) := sorry
    example : (¬p ∨ q) → (p → q) := sorry
    example : p ∨ False ↔ p := sorry
    example : p ∧ False ↔ False := sorry
    example : (p → q) → (¬q → ¬p) := sorry

    /- 2. -/
    namespace WithClassical
      open Classical

      variable (p q r : Prop)

      example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := sorry
      example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
      example : ¬(p → q) → p ∧ ¬q := sorry
      example : (p → q) → (¬p ∨ q) := sorry
      example : (¬q → ¬p) → (p → q) := sorry
      example : p ∨ ¬p := sorry
      example : (((p → q) → p) → p) := sorry
    end WithClassical

    /- 3. Prove ¬(p ↔ ¬p) without using classical logic.  -/
    example : ¬(p ↔ ¬p) := sorry
  end Chapter3WithTactics

  namespace Chapter4WithTactics
    /- 1. Prove these equivalences -/
    variable (α : Type) (p q : α → Prop)
    example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
      Iff.intro
        (fun h : ∀ x, p x ∧ q x =>
          And.intro
            (fun x : α => (h x).left)
            (fun x : α => (h x).right)
        )
        (fun h : (∀ x, p x) ∧ (∀ x, q x) =>
          (fun x : α =>
            And.intro (h.left x) (h.right x)
          )
        )

    example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
      (fun hxpq : ∀ x, p x → q x =>
        (fun hxp : ∀ x, p x =>
          (fun x : α =>
            (hxpq x) (hxp x)
          )
        )
      )

    example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
      (fun hxpxq : (∀ x, p x) ∨ (∀ x, q x) =>
        (fun x : α =>
          Or.elim hxpxq
            (fun hxp : ∀ x, p x => Or.inl (hxp x))
            (fun hxq : ∀ x, q x => Or.inr (hxq x))
        )
      )

    /- 2. It is often possible to bring a component of a formula outside a universal quantifier, when it does not depend on the quantified variable. Try proving these (one direction of the second of these requires classical logic): -/
    variable (α : Type) (p q : α → Prop)
    variable (r : Prop)

    example : α → ((∀ x : α, r) ↔ r) := sorry
    example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry
    example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := sorry

    /- 3. Consider the “barber paradox,” that is, the claim that in a certain town there is a (male) barber that shaves all and only the men who do not shave themselves. Prove that this is a contradiction: -/
    variable (men : Type) (barber : men)
    variable (shaves : men → men → Prop)

    example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := sorry

    /- 4. Remember that, without any parameters, an expression of type Prop is just an assertion. Fill in the definitions of prime and Fermat_prime below, and construct each of the given assertions. For example, you can say that there are infinitely many primes by asserting that for every natural number n, there is a prime number greater than n. Goldbach's weak conjecture states that every odd number greater than 5 is the sum of three primes. Look up the definition of a Fermat prime or any of the other statements, if necessary. -/
    def even (n : Nat) : Prop := sorry
    def prime (n : Nat) : Prop := sorry
    def infinitely_many_primes : Prop := sorry
    def Fermat_prime (n : Nat) : Prop := sorry
    def infinitely_many_Fermat_primes : Prop := sorry
    def goldbach_conjecture : Prop := sorry
    def Goldbach's_weak_conjecture : Prop := sorry
    def Fermat's_last_theorem : Prop := sorry

    /- 5. Prove as many of the identities listed in the Existential Quantifier section as you can. -/
    namespace WithClassical
      open Classical

      variable (α : Type) (p q : α → Prop)
      variable (r : Prop)

      example : (∃ x : α, r) → r := sorry
      example (a : α) : r → (∃ x : α, r) := sorry
      example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := sorry
      example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := sorry

      example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry
      example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
      example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
      example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

      example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
      example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
      example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
    end WithClassical
  end Chapter4WithTactics

  example (p q r : Prop) (hp : p) : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
    sorry
end Chapter5

namespace Chapter7
  /-
  1. Try defining other operations on the natural numbers, such as multiplication, the predecessor function (with pred 0 = 0), truncated subtraction (with n - m = 0 when m is greater than or equal to n), and exponentiation. Then try proving some of their basic properties, building on the theorems we have already proved.
     Since many of these are already defined in Lean's core library, you should work within a namespace named Hidden, or something like that, in order to avoid name clashes.

  2. Define some operations on lists, like a length function or the reverse function. Prove some properties, such as the following:
     a. length (xs ++ ys) = length xs + length ys
     b. length (reverse xs) = length xs
     c. reverse (reverse xs) = xs

  3. Define an inductive data type consisting of terms built up from the following constructors:
     * const n, a constant denoting the natural number n
     * var n, a variable, numbered n
     * plus s t, denoting the sum of s and t
     * times s t, denoting the product of s and t

     Recursively define a function that evaluates any such term with respect to an assignment of values to the variables.

  4. Similarly, define the type of propositional formulas, as well as functions on the type of such formulas: an evaluation function, functions that measure the complexity of a formula, and a function that substitutes another formula for a given variable.
  -/
end Chapter7
