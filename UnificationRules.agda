open import PathPrelude
open import Prelude.Empty
open import Prelude.Unit
open import Prelude.Nat
open import Prelude.Function

NoConfusion : Nat → Nat → Set
NoConfusion zero zero = ⊤
NoConfusion zero (suc y) = ⊥
NoConfusion (suc x) zero = ⊥
NoConfusion (suc x) (suc y) = x ≡ y

noConfusion : (x y : Nat) → x ≡ y → NoConfusion x y
noConfusion x y p =
  subst p
    (case x return (λ x → NoConfusion x x) of λ where
      zero    → unit
      (suc x) → refl)

noConfusion⁻¹ : (x y : Nat) → NoConfusion x y → x ≡ y
noConfusion⁻¹ zero    zero    unit = refl
noConfusion⁻¹ zero    (suc y) ()
noConfusion⁻¹ (suc x) zero    ()
noConfusion⁻¹ (suc x) (suc y) p    = cong suc p

dcong : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} (f : (x : A) → B x)
      → {x y : A} (p : x ≡ y) → PathP (λ i → B (p i)) (f x) (f y)
dcong f p i = f (p i)

noConfusionLinv : (x y : Nat) (p : x ≡ y) → noConfusion⁻¹ x y (noConfusion x y p) ≡ p
noConfusionLinv x y p =
  pathJ (λ y p → noConfusion⁻¹ x y (noConfusion x y p) ≡ p)
    (case x return (λ x → noConfusion⁻¹ x x (noConfusion x x refl) ≡ refl) of λ where
      zero    → refl
      (suc x) → dcong (cong suc) {noConfusion (suc x) (suc x) refl} {refl}
                  (pathJprop (λ y _ → NoConfusion (suc x) (suc y)) refl))
    y p

noConfusionRinv : (x y : Nat) (p : NoConfusion x y) → noConfusion x y (noConfusion⁻¹ x y p) ≡ p
noConfusionRinv zero zero unit = refl
noConfusionRinv zero (suc y) ()
noConfusionRinv (suc x) zero ()
noConfusionRinv (suc x) (suc y) p =
  pathJ (λ y p → noConfusion (suc x) (suc y) (cong suc p) ≡ p)
    (pathJprop (λ y _ → NoConfusion (suc x) (suc y)) refl)
    y p

-- an example unification rule
suc-injective : (x y : Nat) → (suc x ≡ suc y) → (x ≡ y)
suc-injective x y p = noConfusion (suc x) (suc y) p

suc-injective⁻¹ : (x y : Nat) → (x ≡ y) → (suc x ≡ suc y)
suc-injective⁻¹ x y p = noConfusion⁻¹ (suc x) (suc y) p

suc-injective-linv : (x y : Nat) (p : suc x ≡ suc y)
                   → noConfusion⁻¹ (suc x) (suc y) (noConfusion (suc x) (suc y) p) ≡ p
suc-injective-linv x y = noConfusionLinv (suc x) (suc y)

suc-injective-rinv : (x y : Nat) (p : NoConfusion (suc x) (suc y))
                   → noConfusion (suc x) (suc y) (noConfusion⁻¹ (suc x) (suc y) p) ≡ p
suc-injective-rinv x y = noConfusionRinv (suc x) (suc y)

-- properties of a strong unification rule
module StrongRuleProps where
  prop₁ : (x : Nat) → suc-injective x x refl ≡ refl
  prop₁ x = {!refl!}

  prop₂ : (x : Nat) → suc-injective⁻¹ x x refl ≡ refl
  prop₂ x = refl

  prop₃ : (x : Nat) → suc-injective-linv x x refl ≡ {!refl!}
  prop₃ x = {!refl!}

  prop₄ : (x : Nat) → suc-injective-rinv x x refl ≡ {!refl!}
  prop₄ x = {!refl!}
