-- Formalization of https://arxiv.org/abs/1504.05531
-- Homotopy-initial algebras in type theory
{-# OPTIONS --without-K #-}
module hinitiality-3 where
open import Level
open import Base
open import Ch3
open import Ch4
open import hinitiality-2

-- Definition 3.1
isind : ∀ {ℓ ℓ'} → (A : Bip {ℓ}) → Set _
isind {ℓ} {ℓ'} A = (E : FibBip {ℓ' = ℓ'} A) → BipSec A E

BipInd : ∀ {ℓ ℓ'} → Set _
BipInd {ℓ} {ℓ'} = Σ[ A ∈ Bip {ℓ} ] isind {ℓ' = ℓ'} A

-- Proposition 3.2
elim : ∀ {ℓ ℓ'} {A : Bip {ℓ}} (AisInd : isind {ℓ' = ℓ'} A) (E : pr₁ A → Set ℓ')
     → (x : pr₁ A) (e₀ : E (pr₁ (pr₂ A))) (e₁ : E (pr₂ (pr₂ A))) → E x
elim {A = (A , a₀ , a₁)} AisInd E x e₀ e₁ = pr₁ (AisInd (E , e₀ , e₁)) x

comp₀ : ∀ {ℓ ℓ'} {A : Bip {ℓ}} (AisInd : isind {ℓ' = ℓ'} A) (E : pr₁ A → Set ℓ')
      → (e₀ : E (pr₁ (pr₂ A))) (e₁ : E (pr₂ (pr₂ A)))
      → elim AisInd E (pr₁ (pr₂ A)) e₀ e₁ ≡ e₀
comp₀ {A = (A , a₀ , a₁)} AisInd E e₀ e₁ = pr₁ (pr₂ (AisInd (E , e₀ , e₁)))

comp₁ : ∀ {ℓ ℓ'} {A : Bip {ℓ}} (AisInd : isind {ℓ' = ℓ'} A) (E : pr₁ A → Set ℓ')
      → (e₀ : E (pr₁ (pr₂ A))) (e₁ : E (pr₂ (pr₂ A)))
      → elim AisInd E (pr₂ (pr₂ A)) e₀ e₁ ≡ e₁
comp₁ {A = (A , a₀ , a₁)} AisInd E e₀ e₁ = pr₂ (pr₂ (AisInd (E , e₀ , e₁)))

-- Proposition 3.3
η : ∀ {ℓ ℓ'} {A : Bip {ℓ}} (AisInd : isind {ℓ' = ℓ'} A) (E : pr₁ A → Set ℓ')
  → (e₀ : E (pr₁ (pr₂ A))) (e₁ : E (pr₂ (pr₂ A)))
  → (f : (x : pr₁ A) → E x) → f (pr₁ (pr₂ A)) ≡ e₀ → f (pr₂ (pr₂ A)) ≡ e₁
  → (x : pr₁ A) → (f x) ≡ elim AisInd E x e₀ e₁
η {A = (A , a₀ , a₁)} AisInd E e₀ e₁ f f₀ f₁ x = elim AisInd F x p₀ p₁
  where
  F : A → Set _
  F x = f x ≡ elim AisInd E x e₀ e₁

  p₀ = f₀ ▪ comp₀ AisInd E e₀ e₁ ⁻¹
  p₁ = f₁ ▪ comp₁ AisInd E e₀ e₁ ⁻¹

η₀ : ∀ {ℓ ℓ'} {A : Bip {ℓ}} (AisInd : isind {ℓ' = ℓ'} A) (E : pr₁ A → Set ℓ')
   → (e₀ : E (pr₁ (pr₂ A))) (e₁ : E (pr₂ (pr₂ A)))
   → (f : (x : pr₁ A) → E x) → (f₀ : f (pr₁ (pr₂ A)) ≡ e₀) → (f₁ : f (pr₂ (pr₂ A)) ≡ e₁)
   → η AisInd E e₀ e₁ f f₀ f₁ (pr₁ (pr₂ A)) ▪ comp₀ AisInd E e₀ e₁ ≡ f₀
η₀ {A = (A , a₀ , a₁)} AisInd E e₀ e₁ f f₀ f₁ = ap (λ x → x ▪ comp₀ AisInd E e₀ e₁) (comp₀ AisInd F p₀ p₁)
                                              ▪ assoc▪ _ _ _ ⁻¹
                                              ▪ ap (λ x → f₀ ▪ x) (p⁻¹▪p≡refly _)
                                              ▪ unit-right _ ⁻¹
  where
  F : A → Set _
  F x = f x ≡ elim AisInd E x e₀ e₁

  p₀ = f₀ ▪ comp₀ AisInd E e₀ e₁ ⁻¹
  p₁ = f₁ ▪ comp₁ AisInd E e₀ e₁ ⁻¹

η₁ : ∀ {ℓ ℓ'} {A : Bip {ℓ}} (AisInd : isind {ℓ' = ℓ'} A) (E : pr₁ A → Set ℓ')
   → (e₀ : E (pr₁ (pr₂ A))) (e₁ : E (pr₂ (pr₂ A)))
   → (f : (x : pr₁ A) → E x) → (f₀ : f (pr₁ (pr₂ A)) ≡ e₀) → (f₁ : f (pr₂ (pr₂ A)) ≡ e₁)
   → η AisInd E e₀ e₁ f f₀ f₁ (pr₂ (pr₂ A)) ▪ comp₁ AisInd E e₀ e₁ ≡ f₁
η₁ {A = (A , a₀ , a₁)} AisInd E e₀ e₁ f f₀ f₁ = ap (λ x → x ▪ comp₁ AisInd E e₀ e₁) (comp₁ AisInd F p₀ p₁)
                                              ▪ assoc▪ _ _ _ ⁻¹
                                              ▪ ap (λ x → f₁ ▪ x) (p⁻¹▪p≡refly _)
                                              ▪ unit-right _ ⁻¹
  where
  F : A → Set _
  F x = f x ≡ elim AisInd E x e₀ e₁

  p₀ = f₀ ▪ comp₀ AisInd E e₀ e₁ ⁻¹
  p₁ = f₁ ▪ comp₁ AisInd E e₀ e₁ ⁻¹

-- Proposition 3.4
isind→isPropBipSec : ∀ {ℓ ℓ'} {A : Bip {ℓ}} (AisInd : isind {ℓ' = ℓ'} A)
                   → (E : FibBip {ℓ' = ℓ'} A)
                   → (f g : BipSec A E) → f ≡ g
isind→isPropBipSec {A = (A , a₀ , a₁)} AisInd (E , e₀ , e₁) (f , f₀ , f₁) (g , g₀ , g₁) =
  ≃← (BipSec≃ _ _) ((λ x → ηf x ▪ ηg x ⁻¹) , η₀' , η₁')
  where
  ηf = η AisInd E e₀ e₁ f f₀ f₁
  ηg = η AisInd E e₀ e₁ g g₀ g₁
  ηf₀ = η₀ AisInd E e₀ e₁ f f₀ f₁
  ηf₁ = η₁ AisInd E e₀ e₁ f f₀ f₁
  ηg₀ = η₀ AisInd E e₀ e₁ g g₀ g₁
  ηg₁ = η₁ AisInd E e₀ e₁ g g₀ g₁
  com₀ = comp₀ AisInd E e₀ e₁
  com₁ = comp₁ AisInd E e₀ e₁

  η₀' : f₀ ≡ ηf a₀ ▪ ηg a₀ ⁻¹ ▪ g₀
  η₀' = l-cancel {r = ηf a₀ ⁻¹} _ _
        (ηf a₀ ⁻¹ ▪ f₀
      ≡⟨ ap (λ x → ηf a₀ ⁻¹ ▪ x) (ηf₀ ⁻¹) ⟩
         ηf a₀ ⁻¹ ▪ (ηf a₀ ▪ com₀)
      ≡⟨ assoc▪ _ _ _ ▪ ap (λ x → x ▪ com₀) (p⁻¹▪p≡refly _) ⟩
         refl _ ▪ com₀
      ≡⟨ ap (λ x → x ▪ com₀) (p⁻¹▪p≡refly _ ⁻¹) ▪ assoc▪ _ _ _ ⁻¹ ▪ ap (λ x → ηg a₀ ⁻¹ ▪ x) ηg₀ ⟩
         ηg a₀ ⁻¹ ▪ g₀
      ≡⟨ unit-left (ηg a₀ ⁻¹ ▪ g₀) ▪ assoc▪ _ _ _ ▪ ap (λ x → x  ▪ ηg a₀ ⁻¹ ▪ g₀) (p⁻¹▪p≡refly _ ⁻¹) ⟩
         ηf a₀ ⁻¹ ▪ ηf a₀ ▪ ηg a₀ ⁻¹ ▪ g₀
      ≡⟨ ap (λ x → x ▪ g₀) (assoc▪ _ _ _ ⁻¹) ▪ assoc▪ _ _ _ ⁻¹ ⟩
         ηf a₀ ⁻¹ ▪ (ηf a₀ ▪ ηg a₀ ⁻¹ ▪ g₀) ∎)

  η₁' : f₁ ≡ ηf a₁ ▪ ηg a₁ ⁻¹ ▪ g₁
  η₁' = l-cancel {r = ηf a₁ ⁻¹} _ _
        (ηf a₁ ⁻¹ ▪ f₁
      ≡⟨ ap (λ x → ηf a₁ ⁻¹ ▪ x) (ηf₁ ⁻¹) ⟩
         ηf a₁ ⁻¹ ▪ (ηf a₁ ▪ com₁)
      ≡⟨ assoc▪ _ _ _ ▪ ap (λ x → x ▪ com₁) (p⁻¹▪p≡refly _) ⟩
         refl _ ▪ com₁
      ≡⟨ ap (λ x → x ▪ com₁) (p⁻¹▪p≡refly _ ⁻¹) ▪ assoc▪ _ _ _ ⁻¹ ▪ ap (λ x → ηg a₁ ⁻¹ ▪ x) ηg₁ ⟩
         ηg a₁ ⁻¹ ▪ g₁
      ≡⟨ unit-left (ηg a₁ ⁻¹ ▪ g₁) ▪ assoc▪ _ _ _ ▪ ap (λ x → x  ▪ ηg a₁ ⁻¹ ▪ g₁) (p⁻¹▪p≡refly _ ⁻¹) ⟩
         ηf a₁ ⁻¹ ▪ ηf a₁ ▪ ηg a₁ ⁻¹ ▪ g₁
      ≡⟨ ap (λ x → x ▪ g₁) (assoc▪ _ _ _ ⁻¹) ▪ assoc▪ _ _ _ ⁻¹ ⟩
         ηf a₁ ⁻¹ ▪ (ηf a₁ ▪ ηg a₁ ⁻¹ ▪ g₁) ∎)

isindIsProp : ∀ {ℓ ℓ'} {A : Bip {ℓ}} → isProp (isind {ℓ' = ℓ'} A)
isindIsProp {ℓ} {ℓ'} {A} AisInd _ = ΠisProp (isind→isPropBipSec AisInd) _ _

-- Definition 3.5
ishinit : ∀ {ℓ ℓ'} (A : Bip {ℓ}) → Set _
ishinit {ℓ' = ℓ'} A = (B : Bip {ℓ = ℓ'}) → isContr (Bipmorphism A B)

-- Proposition 3.6
ishinitIsProp : ∀ {ℓ ℓ'} (A : Bip {ℓ}) → isProp (ishinit {ℓ' = ℓ'} A)
ishinitIsProp A = ΠisProp (λ B → isContrAisProp)

-- Proposition 3.7
hinit-uniqiso : ∀ {ℓ} (A : Bip {ℓ}) (B : Bip {ℓ})
              → ishinit {ℓ' = ℓ} A × ishinit {ℓ' = ℓ} B → isContr (BipEquiv A B)
hinit-uniqiso A B (Aishinit , Bishinit) = ≃isContr (isProp→isContra (isbipequivIsProp , beq)) (eq ⁻¹≃)
  where
  beq : isbipequiv {A = A} {B = B} (pr₁ (Aishinit B))
  beq with (Aishinit B) | (Bishinit A)
  ... | (f , _) | (g , _) = (g , pr₂ (Aishinit A) (_∘b_ {A = A} {B = B} {C = A} g f) ⁻¹ ▪ pr₂ (Aishinit A) (idBip {A = A}))
                          , (g , pr₂ (Bishinit B) (_∘b_ {A = B} {B = A} {C = B} f g) ⁻¹ ▪ pr₂ (Bishinit B) (idBip {A = B}))

  eq : BipEquiv A B ≃ isbipequiv {A = A} {B = B} (pr₁ (Aishinit B))
  eq = isContrA→ΣPx≃Pa (Bipmorphism A B) (isbipequiv {A = A} {B = B}) (Aishinit B)

-- Proposition 3.8
rec : ∀ {ℓ ℓ'} {A : Bip {ℓ}} → ishinit {ℓ' = ℓ'} A → (B : Set ℓ')
    → (a : pr₁ A) (b₀ : B) (b₁ : B) → B
rec {A = A} Aishinit B a b₀ b₁ = pr₁ f a
  where
  f : Bipmorphism A (B , b₀ , b₁)
  f = pr₁ (Aishinit (B , b₀ , b₁))

β₀ : ∀ {ℓ ℓ'} {A : Bip {ℓ}} → (Aishinit : ishinit {ℓ' = ℓ'} A) → (B : Set ℓ')
   → (b₀ : B) (b₁ : B) → rec {A = A} Aishinit B (pr₁ (pr₂ A)) b₀ b₁ ≡ b₀
β₀ {A = A} Aishinit B b₀ b₁ = pr₁ (pr₂ f)
  where
  f : Bipmorphism A (B , b₀ , b₁)
  f = pr₁ (Aishinit (B , b₀ , b₁))

β₁ : ∀ {ℓ ℓ'} {A : Bip {ℓ}} → (Aishinit : ishinit {ℓ' = ℓ'} A) → (B : Set ℓ')
   → (b₀ : B) (b₁ : B) → rec {A = A} Aishinit B (pr₂ (pr₂ A)) b₀ b₁ ≡ b₁
β₁ {A = A} Aishinit B b₀ b₁ = pr₂ (pr₂ f)
  where
  f : Bipmorphism A (B , b₀ , b₁)
  f = pr₁ (Aishinit (B , b₀ , b₁))

η' : ∀ {ℓ ℓ'} {A : Bip {ℓ}} → (Aishinit : ishinit {ℓ' = ℓ'} A)
   → (B : Bip {ℓ'}) → (f : Bipmorphism A B)
   → (x : pr₁ A) → (pr₁ f) x ≡ rec {A = A} Aishinit (pr₁ B) x (pr₁ (pr₂ B)) (pr₂ (pr₂ B))
η' {A = A} Aishinit B f x = ap (λ h → h x) (pr₁ q)
   where
   recmorphism : Bipmorphism A B
   recmorphism = (λ x → rec {A = A} Aishinit (pr₁ B) x (pr₁ (pr₂ B)) (pr₂ (pr₂ B)))
               , β₀ {A = A} Aishinit (pr₁ B) (pr₁ (pr₂ B)) (pr₂ (pr₂ B))
               , β₁ {A = A} Aishinit (pr₁ B) (pr₁ (pr₂ B)) (pr₂ (pr₂ B))
               
   p : f ≡ recmorphism
   p = (pr₂ (Aishinit B) f ⁻¹ ▪ pr₂ (Aishinit B) recmorphism)
   q = pairΣ≡⁻¹ p


η₀' : ∀ {ℓ ℓ'} {A : Bip {ℓ}} → (Aishinit : ishinit {ℓ' = ℓ'} A)
    → (B : Bip {ℓ'}) → (f : Bipmorphism A B)
    → η' {A = A} Aishinit B f (pr₁ (pr₂ A))
    ▪ β₀ {A = A} Aishinit (pr₁ B) (pr₁ (pr₂ B)) (pr₂ (pr₂ B)) ≡ pr₁ (pr₂ f)
η₀' {A = (A , a₀ , a₁)} Aishinit (B , b₀ , b₁) (f , f₀ , f₁) =
    η'' ▪ β'
 ≡⟨ ap (λ x → x ▪ β') (p⁻¹⁻¹≡p η'' ⁻¹) ⟩
    η'' ⁻¹ ⁻¹ ▪ β'
 ≡⟨ (transport[x↦x≡a] b₀ (η'' ⁻¹) β') ⁻¹ ⟩
    transport (λ x → x ≡ b₀) (ap (λ h → h a₀) (pr₁ q) ⁻¹) β'
 ≡⟨ ap (λ p₁ → transport (λ x → x ≡ b₀) p₁ β') (ap⁻¹ (λ h → h a₀) _ _ (pr₁ q) ⁻¹) ⟩
    transport (λ x → x ≡ b₀) (ap (λ h → h a₀) ((pr₁ q) ⁻¹)) β'
 ≡⟨ transport[P∘f] (λ h → h a₀) (λ x → x ≡ b₀) (pr₁ q ⁻¹) β' ⁻¹ ⟩
    transport (λ h → h a₀ ≡ b₀) (pr₁ q ⁻¹) β'
 ≡⟨ (≃→ (idtoeqv ([p*q≡r]≡[q≡p⁻¹*r] {p = pr₁ q} {q = f₀} {r = β'})) r) ⁻¹ ⟩
    f₀ ∎
    where
    β' = β₀ {A = (A , a₀ , a₁)} Aishinit B b₀ b₁
    η'' = η' {A = (A , a₀ , a₁)} Aishinit (B , b₀ , b₁) (f , f₀ , f₁) a₀
    recmorphism : Bipmorphism (A , a₀ , a₁) (B , b₀ , b₁)
    recmorphism = (λ x → rec {A = (A , a₀ , a₁)} Aishinit B x b₀ b₁)
                , β₀ {A = (A , a₀ , a₁)} Aishinit B b₀ b₁
                , β₁ {A = (A , a₀ , a₁)} Aishinit B b₀ b₁

    p : f , f₀ , f₁ ≡ recmorphism
    p = (pr₂ (Aishinit (B , b₀ , b₁)) (f , f₀ , f₁) ⁻¹ ▪ pr₂ (Aishinit (B , b₀ , b₁)) recmorphism)
    q = pairΣ≡⁻¹ p
    r : (pr₁ q *) f₀ ≡ β'
    r = ap pr₁ (transport× (pr₁ q) (f₀ , f₁)) ⁻¹ ▪ pr₁ (pair×≡⁻¹ (pr₂ q))

η₁' : ∀ {ℓ ℓ'} {A : Bip {ℓ}} → (Aishinit : ishinit {ℓ' = ℓ'} A)
    → (B : Bip {ℓ'}) → (f : Bipmorphism A B)
    → η' {A = A} Aishinit B f (pr₂ (pr₂ A))
    ▪ β₁ {A = A} Aishinit (pr₁ B) (pr₁ (pr₂ B)) (pr₂ (pr₂ B)) ≡ pr₂ (pr₂ f)
η₁' {A = (A , a₀ , a₁)} Aishinit (B , b₀ , b₁) (f , f₀ , f₁) =
    η'' ▪ β'
 ≡⟨ ap (λ x → x ▪ β') (p⁻¹⁻¹≡p η'' ⁻¹) ⟩
    η'' ⁻¹ ⁻¹ ▪ β'
 ≡⟨ (transport[x↦x≡a] b₁ (η'' ⁻¹) β') ⁻¹ ⟩
    transport (λ x → x ≡ b₁) (ap (λ h → h a₁) (pr₁ q) ⁻¹) β'
 ≡⟨ ap (λ p₁ → transport (λ x → x ≡ b₁) p₁ β') (ap⁻¹ (λ h → h a₁) _ _ (pr₁ q) ⁻¹) ⟩
    transport (λ x → x ≡ b₁) (ap (λ h → h a₁) ((pr₁ q) ⁻¹)) β'
 ≡⟨ transport[P∘f] (λ h → h a₁) (λ x → x ≡ b₁) (pr₁ q ⁻¹) β' ⁻¹ ⟩
    transport (λ h → h a₁ ≡ b₁) (pr₁ q ⁻¹) β'
 ≡⟨ (≃→ (idtoeqv ([p*q≡r]≡[q≡p⁻¹*r] {p = pr₁ q} {q = f₁} {r = β'})) r) ⁻¹ ⟩
    f₁ ∎
    where
    β' = β₁ {A = (A , a₀ , a₁)} Aishinit B b₀ b₁
    η'' = η' {A = (A , a₀ , a₁)} Aishinit (B , b₀ , b₁) (f , f₀ , f₁) a₁
    recmorphism : Bipmorphism (A , a₀ , a₁) (B , b₀ , b₁)
    recmorphism = (λ x → rec {A = (A , a₀ , a₁)} Aishinit B x b₀ b₁)
                , β₀ {A = (A , a₀ , a₁)} Aishinit B b₀ b₁
                , β₁ {A = (A , a₀ , a₁)} Aishinit B b₀ b₁

    p : f , f₀ , f₁ ≡ recmorphism
    p = (pr₂ (Aishinit (B , b₀ , b₁)) (f , f₀ , f₁) ⁻¹ ▪ pr₂ (Aishinit (B , b₀ , b₁)) recmorphism)
    q = pairΣ≡⁻¹ p
    r : (pr₁ q *) f₁ ≡ β'
    r = ap pr₂ (transport× (pr₁ q) (f₀ , f₁)) ⁻¹ ▪ pr₂ (pair×≡⁻¹ (pr₂ q))

-- Theorem 3.10
isind→ishinit : ∀ {ℓ ℓ'} {A : Bip {ℓ}} → isind {ℓ' = ℓ'} A → ishinit {ℓ' = ℓ'} A
isind→ishinit {A = (A , a₀ , a₁)} Aisind (B , b₀ , b₁) = sec , isind→isPropBipSec Aisind ((λ x → B) , b₀ , b₁) sec
  where
  sec : BipSec (A , a₀ , a₁) ((λ x → B) , b₀ , b₁)
  sec = Aisind ((λ x → B) , b₀ , b₁)

ishinit→isind : ∀ {ℓ ℓ'} {A : Bip {ℓ}} → (ishinit {ℓ' = ℓ' ⊔ ℓ} A × ishinit {ℓ' = ℓ} A)
              → isind {ℓ' = ℓ'} A
ishinit→isind {A = 𝑨@(A , a₀ , a₁)} (Aishinit , Aishinitℓ) 𝑬@(E , e₀ , e₁) = s , s₀ , s₁
  where
  E' : Bip
  E' = ((Σ[ x ∈ A ] (E x)) , (a₀ , e₀) , (a₁ , e₁))

  π₁ : Bipmorphism E' 𝑨
  π₁ = pr₁ , refl a₀ , refl a₁

  f : Bipmorphism 𝑨 E'
  f = pr₁ (Aishinit E')

  π₁∘f : Bipmorphism 𝑨 𝑨
  π₁∘f = _∘b_ {A = 𝑨} {B = E'} {C = 𝑨} π₁ f
  idA = idBip {A = 𝑨}

  π₁∘f≡id : π₁∘f ≡ idA
  π₁∘f≡id = pr₂ (Aishinitℓ 𝑨) π₁∘f ⁻¹ ▪ pr₂ (Aishinitℓ 𝑨) idA

  α : Bip~ {A = 𝑨} {B = 𝑨} π₁∘f idA
  α = ≃→ (Bip≃ {A = 𝑨} {B = 𝑨} π₁∘f idA) π₁∘f≡id

  s : (x : A) → E x
  s x with f | α
  ... | (f , f₀ , f₁) | (α , α₀ , α₁) = transport E (α x) (pr₂ (f x))

  s₀ : s a₀ ≡ e₀
  s₀ with f | α
  ... | (f , f₀ , f₁) | (α , α₀ , α₁) = transport E (α a₀) (pr₂ (f a₀))
                                     ≡⟨ ap (λ p₁ → transport E p₁ (pr₂ (f a₀))) r ⟩
                                        transport E p (pr₂ (f a₀))
                                     ≡⟨ pr₂ (pairΣ≡⁻¹ f₀) ⟩
                                        e₀ ∎
    where
    p = pr₁ (pairΣ≡⁻¹ f₀)

    r : α a₀ ≡ p
    r = r-cancel _ _ α₀ ⁻¹ ▪ pairΣ≡₁' f₀

  s₁ : s a₁ ≡ e₁
  s₁ with f | α
  ... | (f , f₀ , f₁) | (α , α₀ , α₁) = transport E (α a₁) (pr₂ (f a₁))
                                     ≡⟨ ap (λ p₁ → transport E p₁ (pr₂ (f a₁))) r ⟩
                                        transport E p (pr₂ (f a₁))
                                     ≡⟨ pr₂ (pairΣ≡⁻¹ f₁) ⟩
                                        e₁ ∎
    where
    p = pr₁ (pairΣ≡⁻¹ f₁)

    r : α a₁ ≡ p
    r = r-cancel _ _ α₁ ⁻¹ ▪ pairΣ≡₁' f₁

-- Corollary 3.12
𝟚ishinit : ∀ {ℓ} → ishinit {ℓ' = ℓ} (𝟚 , 0₂ , 1₂)
𝟚ishinit = isind→ishinit {A = (𝟚 , 0₂ , 1₂)} 𝟚isind
  where
  𝟚isind : isind (𝟚 , 0₂ , 1₂)
  𝟚isind (E , e₀ , e₁) = ind𝟚 E e₀ e₁ , refl e₀ , refl e₁

-- Theorem 3.14
uaBip : ∀ {ℓ} {A B : Bip {ℓ}} → A ≡ B ≃ BipEquiv A B
uaBip {A = 𝑨@(A , a₀ , a₁)} {B = 𝑩@(B , b₀ , b₁)} =
      𝑨 ≡ 𝑩
   ≃⟨ Σ≃ ⟩
      Σ[ p ∈ (A ≡ B) ] (p *) (a₀ , a₁) ≡ (b₀ , b₁)
   ≃⟨ ≃→Σ≃ (λ p → idtoeqv (ap (λ x → x ≡ (b₀ , b₁)) (transport× p (a₀ , a₁)))
               ▪≃ (pair×≡⁻¹ , ×≃)) ⟩
      Σ[ p ∈ (A ≡ B) ] ((((p *) a₀) ≡ b₀) × (((p *) a₁) ≡ b₁))
   ≃⟨ ≃→Σ≃ (λ p → ≃→×≃ (idtoeqv (ap (λ x → x ≡ b₀) (ap (λ p → (p *) a₀) (uniq≡ p) ▪ computation≡ (idtoeqv p) a₀)))
                       (idtoeqv (ap (λ x → x ≡ b₁) (ap (λ p → (p *) a₁) (uniq≡ p) ▪ computation≡ (idtoeqv p) a₁)))) ⟩
      Σ[ p ∈ (A ≡ B) ] (((≃→ (idtoeqv p) a₀) ≡ b₀) × ((≃→ (idtoeqv p) a₁) ≡ b₁))
   ≃⟨ ≃→≃Σ (idtoeqv , univalence) (λ p → ref≃) ⟩
      Σ[ eq ∈ (A ≃ B) ] (((≃→ eq a₀) ≡ b₀) × ((≃→ eq a₁) ≡ b₁))
   ≃⟨ (λ {((f , eq) , f₀ , f₁) → (f , f₀ , f₁) , eq})
     , qinv→isequiv ( (λ {((f , f₀ , f₁) , eq) → (f , eq) , f₀ , f₁})
                    , (λ {((f , f₀ , f₁) , eq) → refl _})
                    , (λ {((f , eq) , f₀ , f₁) → refl _})) ⟩
      Σ[ f ∈ Bipmorphism 𝑨 𝑩 ] (isequiv (pr₁ f))
   ≃⟨ ≃→Σ≃ (λ f → isbipequiv≃isequiv {A = 𝑨} {B = 𝑩} {f = f} ⁻¹≃) ⟩
      BipEquiv 𝑨 𝑩 ∎≃

-- Corollary 3.15
hinit-uniqpath : ∀ {ℓ} (A : Bip {ℓ}) (B : Bip {ℓ})
               → ishinit {ℓ' = ℓ} A × ishinit {ℓ' = ℓ} B → isContr (A ≡ B)
hinit-uniqpath A B hinit = ≃isContr (hinit-uniqiso A B hinit) (uaBip ⁻¹≃)
