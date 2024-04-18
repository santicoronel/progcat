
module Records where

open import Relation.Binary.PropositionalEquality
open import Axiom.Extensionality.Propositional as Ext

-- postulamos extensionalidad
postulate ext : ∀{a b} → Ext.Extensionality a b

{- Veremos, el uso de records para definir estructuras algebraicas -}


-- MONOIDES

{- Notar el uso de de Set₁ en lugar de Set ya que tenemos que
 situarnos en el nivel siguiente a Set₀ = Set, para hablar de cosas en
 Set (como carrier).

Los subindices son ₀ = \_0 y ₁ = \_1
 -}

record Monoid : Set₁  where
  infixr 7 _∙_
  -- constructor monoid
  field  Carrier : Set
         _∙_     : Carrier → Carrier → Carrier  {- ∙ = \. -}
         ε       : Carrier   {- ε = \epsilon -}
         lid     : {x : Carrier} → ε ∙ x ≡ x
         rid     : {x : Carrier} → x ∙ ε ≡ x
         assoc   : {x y z : Carrier} → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z) 

{- ¿Qué sucede si queremos usar un Carrier en Set₁? ¿o en Set₂? -}

{- Al escribir las ecuaciones estamos tomando una decisión sobre la noción de igualdad 
 En esta definición elegimos la igualdad proposicional
-}

open import Data.Nat
open import Data.Nat.Properties using (+-identityʳ ; +-assoc)

-- Monoide de Naturales y suma

module NatMonoid where


  NatMonoid : Monoid
  NatMonoid = record
    { Carrier = ℕ 
    ; _∙_ = _+_ 
    ; ε = 0 
    ; lid = refl 
    ; rid = λ {x} → +-identityʳ x ; 
    assoc = λ {x} {y} {z} → +-assoc x y z }

open NatMonoid


--------------------------------------------------
{- Ejercicio: Probar que las listas son un monoide -}

open ≡-Reasoning
open import Data.List hiding (foldr ; length)

ridList : {A : Set} (xs : List A) → xs ++ [] ≡ xs
ridList [] = refl
ridList (x ∷ xs) = cong (_∷_ x) (ridList xs)

assocList : {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
assocList [] ys zs = refl
assocList (x ∷ xs) ys zs = cong (_∷_ x) (assocList xs ys zs)

module ListMonoid where

  ListMonoid : Set → Monoid
  ListMonoid A = record
    { Carrier = List A 
    ; _∙_ = _++_
    ; ε = []
    ; lid = refl 
    ; rid = λ {xs} → ridList xs; 
    assoc = λ {xs} {ys} {zs} →  assocList xs ys zs}

open ListMonoid
--------------------------------------------------

{- Ejercicio: Probar que para todo monoide M, N, el producto
   cartesiano de los respectivos soportes (Carrier M × Carrier N)
   es  el soporte de un monoide

 Ayuda : puede ser útil cong₂
-}

open import Data.Product renaming (proj₁ to fst; proj₂ to snd)

module ProdMonoid where 
  

  
  ProdMonoid : Monoid → Monoid → Monoid
  ProdMonoid M₁ M₂ = record
    { Carrier = Monoid.Carrier M₁ × Monoid.Carrier M₂ 
    ; _∙_ = λ {(x₁ , x₂) (y₁ , y₂) → (x₁ ∙₁ y₁) , (x₂ ∙₂ y₂) } 
    ; ε = ε₁ , ε₂ 
    ; lid = λ { {x} → cong₂ (λ x₁ x₂ → x₁ , x₂) l₁ l₂ }
    ; rid = λ { {x} → cong₂ (λ x₁ x₂ → x₁ , x₂) r₁ r₂ } ; 
    assoc = λ { {x} {y} {z} → cong₂ (λ x₁ x₂ → x₁ , x₂) a₁ a₂ } }
    where     
      open Monoid M₁ renaming 
        (Carrier to C₁ ; ε to ε₁ ;  _∙_ to _∙₁_ ; lid to l₁ ; rid to r₁ ; assoc to a₁)
      open Monoid M₂ renaming 
        (Carrier to C₂ ; ε to ε₂ ;  _∙_ to _∙₂_ ; lid to l₂ ; rid to r₂ ; assoc to a₂)

--------------------------------------------------
open import Function

-- Monoide de endofunciones
EndoMonoid : Set → Monoid
EndoMonoid X = record
                 { Carrier = X → X
                 ; _∙_ = _∘′_ 
                 ; ε = id
                 ; lid = refl
                 ; rid = refl
                 ; assoc = refl }


module Cayley where

  open Monoid using (Carrier)

  Cayley : Monoid → Monoid
  Cayley M = EndoMonoid (Carrier M) 

  rep : (M : Monoid) → Carrier M → Carrier (Cayley M)
  rep M x = λ y → x ∙ y
           where open Monoid M

  abs : (M : Monoid) → Carrier (Cayley M) → Carrier M
  abs M f = f ε
           where open Monoid M

  lemma : (M : Monoid) → {x : Carrier M} →
          abs M (rep M x) ≡ x
  lemma M = rid
           where open Monoid M

module Monoid-Homomorphism where
 open Monoid

-- Homomorfismos de monoides
 record Is-Monoid-Homo (M N : Monoid)(morph : Carrier M → Carrier N) : Set₁ where
   open Monoid M renaming (ε to ε₁ ;  _∙_ to _∙₁_)
   open Monoid N renaming (ε to ε₂ ;  _∙_ to _∙₂_)
   field
    preserves-unit : morph ε₁ ≡ ε₂
    preserves-mult : ∀{x y} → morph (x ∙₁ y) ≡ morph x ∙₂ morph y 

open Monoid-Homomorphism
open Cayley

rep-is-monoid-homo : {M : Monoid} → Is-Monoid-Homo M (Cayley M) (rep M)
rep-is-monoid-homo {M} = record {
                         preserves-unit = ext λ x → lid
                       ; preserves-mult = ext (λ x → assoc) }
                  where open Monoid M

--------------------------------------------------
{- Ejercicio: Probar que lengthgth es un homorfismo de monoides -}


length : {A : Set} → List A → ℕ
length [] = 0
length (x ∷ xs) = 1 + length xs


length-++ : {A : Set} → (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
length-++ [] ys = refl
length-++ (x ∷ xs) ys = cong suc (length-++ xs ys) 

length-is-monoid-homo : {A : Set} → Is-Monoid-Homo (ListMonoid A) NatMonoid length
length-is-monoid-homo = record {
                        preserves-unit = refl
                      ; preserves-mult = λ {xs} {ys} → length-++ xs ys }
--------------------------------------------------
{- Ejercicio: Probar que multiplicar por una constante es un es un homorfismo de NatMonoid -}


--------------------------------------------------
module Foldr (M : Monoid) where

 open Monoid M

 {- Ejercicio : Definir foldr y probar que (foldr _∙_ ε) es un homorfismo de monoides -}


 foldr : {A B : Set} → (A → B → B) → B → List A → B
 foldr _⊗_ e [] = e
 foldr _⊗_ e (x ∷ xs) = x ⊗ (foldr _⊗_ e xs)

 foldM : List Carrier → Carrier
 foldM = foldr _∙_ ε 

 foldM-preserves-mult : (xs ys : List Carrier) → foldM (xs ++ ys) ≡ foldM xs ∙ foldM ys
 foldM-preserves-mult [] ys = sym lid
 foldM-preserves-mult (x ∷ xs) ys = 
  begin
    foldM (x ∷ xs ++ ys)
    ≡⟨⟩
    foldM (x ∷ (xs ++ ys))
    ≡⟨⟩
    x ∙ foldM (xs ++ ys) 
    ≡⟨ cong (_∙_ x) (foldM-preserves-mult xs ys) ⟩
    x ∙ (foldM xs ∙ foldM ys) 
    ≡⟨ sym assoc ⟩ 
    (x ∙ foldM xs) ∙ foldM ys 
    ≡⟨⟩ 
    foldM (x ∷ xs) ∙ foldM ys 
    ∎   

 foldM-is-monoid-homo : Is-Monoid-Homo (ListMonoid Carrier) M foldM
 foldM-is-monoid-homo =  record {
                      preserves-unit = refl
                    ; preserves-mult = λ {xs} {ys} → foldM-preserves-mult xs ys } 

--------------------------------------------------

{- Isomorfismos entre conjuntos -}

record Iso (A : Set)(B : Set) : Set where
  field fun : A → B
        inv : B → A
        law1 : ∀ b → fun (inv b) ≡ b
        law2 : ∀ a → inv (fun a) ≡ a

open Iso

-----------------------------

{- Ejercicio : introducir un tipo de datos (record) ⊤ con un único habitante y
probar que  ℕ es isomorfo a List ⊤ -}

record ⊤ : Set where
  constructor ⋆ 

ntimes : {A : Set} → (x : A) → ℕ → List A
ntimes x 0 = []
ntimes x (suc n) = x ∷ ntimes x n

law1-ℕ-List : (xs : List ⊤) → ntimes ⋆ (length xs) ≡ xs
law1-ℕ-List [] = refl
law1-ℕ-List (⋆ ∷ xs) = cong (_∷_ ⋆) (law1-ℕ-List xs)

law2-ℕ-List : (n : ℕ) → length (ntimes ⋆ n) ≡ n
law2-ℕ-List 0 = refl
law2-ℕ-List (suc n) = cong suc (law2-ℕ-List n)

iso-ℕ-List : Iso ℕ (List ⊤)
iso-ℕ-List =  record {
                fun = ntimes ⋆  
              ; inv = length
              ; law1 = law1-ℕ-List
              ; law2 = law2-ℕ-List }  

{- Ejercicio: introducir un constructor de tipos Maybe (o usar Data.Maybe) y probar que
Maybe ℕ es isomorfo a ℕ -}

open import Data.Maybe

ℕ-to-Maybe : ℕ → Maybe ℕ
ℕ-to-Maybe 0 = nothing
ℕ-to-Maybe (suc n) = just n

Maybe-to-ℕ : Maybe ℕ → ℕ
Maybe-to-ℕ nothing = 0
Maybe-to-ℕ (just n) = suc n

law1-ℕ-Maybe : (m : Maybe ℕ) → ℕ-to-Maybe (Maybe-to-ℕ m) ≡ m
law1-ℕ-Maybe nothing = refl
law1-ℕ-Maybe (just n) = refl

law2-ℕ-Maybe : (n : ℕ) → Maybe-to-ℕ (ℕ-to-Maybe n) ≡ n
law2-ℕ-Maybe 0 = refl
law2-ℕ-Maybe (suc n) = refl

iso-ℕ-Maybe : Iso ℕ (Maybe ℕ)
iso-ℕ-Maybe = record {
                fun = ℕ-to-Maybe
              ; inv = Maybe-to-ℕ
              ; law1 = law1-ℕ-Maybe
              ; law2 = law2-ℕ-Maybe }

{- Ejercicio: introducir un constructor de tipos _×_ para productos
cartesianos (o usar el de Data.Product) y probar que (A → B × C) es
isomorfo a (A → B) × (A → C) para todos A, B, y C, habitantes de Set -}


open import Data.Product

iso-Prod : {A B C : Set} → Iso (A → B × C) ((A → B) × (A → C))
iso-Prod =  record {
              fun = λ f → fst ∘ f , snd ∘ f
            ; inv = λ { (f₁ , f₂) → λ x → f₁ x , f₂ x }
            ; law1 = λ { (f₁ , f₂) → refl }
            ; law2 = λ f → refl }

{- Ejercicio: construir isomorfismos entre Vec A n × Vec B n y
Vec (A × B) n para todos A, B habitantes de Set y n natural -}

open import Data.Vec

zipVec : {A B : Set}{n : ℕ} → (Vec A n × Vec B n) → Vec (A × B) n
zipVec ([] ,  []) = []
zipVec (x ∷ xs  , y ∷ ys) = (x , y) ∷ zipVec (xs , ys)

unzipVec : {A B : Set}{n : ℕ} → Vec (A × B) n → Vec A n × Vec B n
unzipVec [] = [] , []
unzipVec ((x , y) ∷ zs) = (x ∷ fst (unzipVec zs)) , (y ∷ snd (unzipVec zs))

law1-Prod-Vec : {A B : Set}{n : ℕ} → (zs : Vec (A × B) n) → zipVec (unzipVec zs) ≡ zs
law1-Prod-Vec [] = refl
law1-Prod-Vec ((x , y) ∷ zs) = cong (_∷_ (x , y)) (law1-Prod-Vec zs)

law2-Prod-Vec : {A B : Set}{n : ℕ} → (z : (Vec A n × Vec B n)) → unzipVec (zipVec z) ≡ z
law2-Prod-Vec ([] , []) = refl
law2-Prod-Vec (x ∷ xs , y ∷ ys) = cong (λ { (us , vs) → x ∷ us , y ∷ vs}) (law2-Prod-Vec (xs , ys))

iso-Prod-Vec : {A B : Set}{n : ℕ} → Iso (Vec A n × Vec B n) (Vec (A × B) n)
iso-Prod-Vec =  record {
                  fun = zipVec 
                ; inv = unzipVec
                ; law1 = law1-Prod-Vec
                ; law2 = law2-Prod-Vec } 




--------------------------------------------------
{- Ejercicio Extra
 Mostrar que en el caso de la categoría Sets, isomorfismo corresponde a biyección de funciones

Ayuda : puede ser útil usar cong-app
-}

Biyectiva : {X Y : Set}(f : X → Y) → Set
Biyectiva {X} {Y} f = (y : Y) → Σ X (λ x → (f x ≡ y) × (∀ x' → f x' ≡ y → x ≡ x')) 

Biyectiva→Iso : {A B : Set}{f : A → B} → Biyectiva f → Iso A B
Biyectiva→Iso {f = f} b = record { 
                            fun = f
                          ; inv = λ y → fst (b y)
                          ; law1 = λ y → fst (snd (b y))
                          ; law2 = λ x → snd (snd (b (f x))) x refl }

Iso→Biyectiva : {A B : Set} → (iso : Iso A B) → Biyectiva (fun iso)
Iso→Biyectiva iso y = inv iso y
                    , law1 iso y
                    , λ x fx≡y →  begin
                                  inv iso y 
                                  ≡⟨ sym (cong  (inv iso) fx≡y) ⟩
                                  inv iso (fun iso x)
                                  ≡⟨ law2 iso x ⟩
                                  x
                                  ∎