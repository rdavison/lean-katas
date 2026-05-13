namespace Chapter3
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

  example : (p → q) → (¬p ∨ q) := sorry
  example : (¬q → ¬p) → (p → q) := sorry
  example : p ∨ ¬p := em p
  example : (((p → q) → p) → p) := sorry
end Chapter3

namespace Chapter4
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
end Chapter4
