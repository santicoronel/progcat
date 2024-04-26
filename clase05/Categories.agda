module Categories where

{- importamos extensionalidad, proof irrelevance -}
open import Library

open import Relation.Binary.PropositionalEquality  


--------------------------------------------------
{- Definición de Categoría -}
{-
 - Una colección de objetos  (denotado con Obj (C))
 - Conjuntos de flechas entre objetos (Sean A, B ∈ Obj(C) , hom (A, B))
 - todo objeto tiene una flecha identidad (id : A → A)
 - todo par de flechas "compatibles" puede componerse ( ∘ )
 - la composición es asociativa, con la flecha identidad como unidad. 
     (f ∘ g) ∘ h = f ∘ (g ∘ h)
     f ∘ id = id ∘ f = f 
-}


record Cat : Set₂ where
  infix 7 _∙_ 
  field Obj : Set₁
        Hom : Obj → Obj → Set
        iden : ∀ {X} → Hom X X
        _∙_ : ∀ {X Y Z} → Hom Y Z → Hom X Y → Hom X Z
        idl : ∀ {X Y} {f : Hom X Y} → iden ∙ f ≡ f  
        idr : ∀ {X Y} {f : Hom X Y} → f ∙ iden ≡ f
        ass : ∀ {X Y Z W} {f : Hom Y Z} {g : Hom X Y}{h : Hom W X} →
              (f ∙ g) ∙ h ≡ f ∙ (g ∙ h)
        

--------------------------------------------------
{- El típico ejemplo de categoría es la categoría Set de conjuntos y
   funciones entre los mismos.
-}


Sets : Cat
Sets = record
         { Obj = Set
         ; Hom = λ X Y → X → Y  
         ; iden = id
         ; _∙_ = λ f g → f ∘ g  
         ; idl = refl
         ; idr = refl
         ; ass = refl
         } 


--------------------------------------------------
{- Para cada categoría existe la categoría dual, que consiste de los
mismos objetos, pero con las flechas invertidas.
   Cₒₚ :  
   Objetos : Obj (C) 
   Hom (X, Y) : Hom (Y, X) ∈ C   

-}

_Op : Cat → Cat
C Op =  let open Cat C in
        record
         { Obj = Obj
         ; Hom = λ X Y → Hom Y X 
         ; iden = iden
         ; _∙_ = λ f g → g ∙ f 
         ; idl = idr
         ; idr = idl
         ; ass = sym ass
         }  



--------------------------------------------------
{- Categoría Discreta

   Una categoría discreta es una categoría en la que los únicos
morfismos son identidades. La composición y ecuaciones de coherencia
son triviales.
-}


Discrete : Set₁ → Cat
Discrete X = record
               { Obj = X
               ; Hom = λ _ _ → ⊤ 
               ; iden = tt  
               ; _∙_ = λ _ _ → tt
               ; idl = refl
               ; idr = refl
               ; ass = refl
               } 



{- A menudo nos queremos "olvidar" de los morfismos de una
categoría. Es decir, miramos a la categoría como una categoría
discreta. Esto se nota en lenguaje categórico como |C| -}

∣_∣ : Cat → Cat
∣ C ∣ = Discrete (Cat.Obj C)

--------------------------------------------------
{- Categoría Producto -}
{- Dadas dos categorías, podemos formar la categoría producto 
   Los objetos son el producto cartesiano de los objetos
   Los morfismos son pares de flechas.


  Obj (C × D) = Obj (C) × Obj(D)
  
         (X , Y) ∈ Obj (C × D) donde X ∈ Obj (C) ∧ y ∈ Obj (D) 

  Hom ((X, Y), (X', Y')) = Hom (X, X') × Hom (Y , Y')

         f : X → X' ∈ Hom (X, X') ∧ g : Y → Y' ∈ Hom (Y, Y') ⇒ (f, g) ∈ Hom ((X, Y), (X', Y'))   

  (f , g) ∘ (f' , g') = (f ∘ f' ,  g ∘ g')
 
  id = (id , id)

-}

_×C_ : Cat → Cat → Cat
C ×C D = record
           { Obj = Obj₁ × Obj₂
           ; Hom = λ {(X , Y) (X' , Y') → Hom₁ X X' × Hom₂ Y Y' }
           ; iden = (iden₁ , iden₂)
           ; _∙_ = λ {(f , g) (f' , g') → f ∙₁ f' , (g ∙₂ g')} 
           ; idl = cong₂ _,_ idl₁ idl₂
           ; idr = cong₂ _,_ idr₁ idr₂
           ; ass = cong₂ _,_ ass₁ ass₂
           } 
           where open Cat C renaming (Obj to Obj₁ ; Hom to Hom₁ ; iden to iden₁ ; _∙_ to _∙₁_ ; idl to idl₁ ; idr to idr₁ ; ass to ass₁)
                 open Cat D renaming (Obj to Obj₂ ; Hom to Hom₂ ; iden to iden₂ ; _∙_ to _∙₂_ ; idl to idl₂ ; idr to idr₂ ; ass to ass₂)  
          


--------------------------------------------------
{- Familia de Conjuntos -}
{- Los objetos son familias de conjuntos
   (conjuntos indexados por un conjunto de índices)

  Los morfismos son funciones que preservan el índice.
 
  Objetos:  {Aᵢ} i ∈ I
  Flechas : Aᵢ → Bᵢ    
-}

Fam : Set → Cat
Fam I = record
          { Obj = I → Set
          ; Hom = λ A B → ∀ {i} → A i → B i  
          ; iden = id
          ; _∙_ = λ f g → f ∘ g  
          ; idl = refl
          ; idr = refl
          ; ass = refl
          } 


--------------------------------------------------
{- Ejemplo extendido: Categorías Slice -}

{- Dada una categoría C, los objetos de un slice
   sobre un objeto I, son morfismos con codominio I
-}


module Slice (C : Cat) where 

  open Cat C

  record Slice₀ (I : Obj) : Set₁ where
    constructor _,_
    field
     base : Obj
     homBase : Hom base I
     
  open Slice₀

  {- record para representar los morfismos de la categoría -}
  record Slice₁ (I : Obj) (X Y : Slice₀ I) : Set where 
    constructor _,_
    field
       baseHom : Hom (base X) (base Y)  -- h  
       prop : (homBase Y) ∙ baseHom ≡ homBase X   -- g ∙ h = f

  {- la composición es simplemente pegar triángulos -}
  Slice-comp :  {I : Obj} {X Y Z : Slice₀ I} →
                Slice₁ I Y Z → Slice₁ I X Y → Slice₁ I X Z
  Slice-comp {I} {X , f} {Y , g} {Z , i} (h , p) (h' , q) =
    ( h ∙ h') , (proof  i ∙ (h ∙ h')
                         ≡⟨ sym ass ⟩
                         (i ∙ h) ∙ h'
                         ≡⟨ cong (λ j → j ∙ h') p ⟩
                         g ∙ h'
                         ≡⟨ q ⟩
                         f
                         ∎ )
  
  open Slice₁

  {- veamos como funciona proof irrelevance -}
  Slice₁-eq : {I : Obj} {X Y : Slice₀ I} {h h' : Slice₁ I X Y} →
              (baseHom h) ≡ (baseHom h')  →
              h ≡ h'
  Slice₁-eq {I} {X , f} {Y , g} {h , p} {.h , q} refl = cong (λ p → (h , p)) (ir p q)
 

  Slice : (I : Obj) → Cat
  Slice I = record
              { Obj = Slice₀ I
              ; Hom = Slice₁ I 
              ; iden = iden , idr
              ; _∙_ = Slice-comp  
              ; idl = Slice₁-eq idl
              ; idr = Slice₁-eq idr
              ; ass = Slice₁-eq ass
              }
 
 
--------------------------------------------------

{- Ejercicio: Definir la categoría con un sólo objeto ⊤, y que sus
morfismos son los elementos de un monoide M -}

module CatMon where

 open import Records-completo hiding (Iso ; ⊤)
 open Monoid

 record ⊤₁ : Set₁ where
   constructor ⋆

 CatMon : Monoid → Cat
 CatMon M = record { 
               Obj = ⊤₁
            ;  Hom = λ { ⋆ ⋆ → Carrier M}
            ;  iden = ε M
            ;  _∙_ = _∙_ M
            ;  idl = lid M
            ;  idr = rid M
            ;  ass = assoc M }


--------------------------------------------------
{- Ejercicio: Definir la categoría en que los objetos son monoides,
  y las flechas son homomorfismos de monoides
-}

module MonCat where

 open import Records-completo hiding (Iso)

 open Is-Monoid-Homo


 ir-mon : {M N : Monoid} (f : Monoid.Carrier M → Monoid.Carrier N ) 
                         → {p : Is-Monoid-Homo M N f} → {q : Is-Monoid-Homo M N f}
                         → p ≡ q
 ir-mon f {p} {q} = proof
                  p
                  ≡⟨⟩
                  is-monoid-homo (preserves-unit p) (preserves-mult p)
                  ≡⟨ cong (λ r → is-monoid-homo r (preserves-mult p))
                          (ir (preserves-unit p) (preserves-unit q)) ⟩
                  is-monoid-homo (preserves-unit q) (preserves-mult p)
                  ≡⟨ cong (λ r → is-monoid-homo (preserves-unit q) (λ {x}{y} → r {x} {y}))
                          (i2ir (preserves-mult p) (preserves-mult q)) ⟩
                  is-monoid-homo (preserves-unit q) (preserves-mult q) 
                  ≡⟨⟩
                  q
                  ∎ 

 MonCat : Cat
 MonCat = record {
           Obj = Monoid
         ; Hom = λ M N → ∃ (Is-Monoid-Homo M N)
         ; iden = id , (is-monoid-homo refl refl)
         ; _∙_ = λ { (f , hf) (g , hg) →
                  f ∘ g , 
                  is-monoid-homo 
                     (trans (cong f (preserves-unit hg)) (preserves-unit hf)) 
                     (λ {x}{y} 
                        → (trans (cong f (preserves-mult hg {x} {y})) (preserves-mult hf {g x} {g y})))
                  }
         ; idl = λ { {f = f , _} → cong (_,_ f) (ir-mon f) }
         ; idr = refl
         ; ass = λ { {f = f , _} {g = g , _} {h = h , _} →  cong (_,_ (f ∘ g ∘ h)) (ir-mon  (f ∘ g ∘ h)) }}
 
--------------------------------------------------
{- Ejercicio: Dada un categoría C, definir la siguiente categoría:
  - Los objetos son morfismos de C
  - Un morfismo entre una flecha f: A → B y f': A'→ B' es un par de morfismos de C
      g1 : A → A', y g2 : B → B', tal que
                    f' ∙ g₁ ≡ g₂ ∙ f
-}

module CommSquare (∁ : Cat) where
 
 open Cat ∁
 
 CommSquare : {A B C D : Obj} → Hom A B → Hom C D → Set
 CommSquare f₁ f₂ = ∃₂ λ g₁ g₂ → f₂ ∙ g₁ ≡ g₂ ∙ f₁

 □-lem : {A B C D E F : Obj}
         {f₁ : Hom A B}{f₂ : Hom C D}{f₃ : Hom E F}
         {g₁ : Hom A C}{g₂ : Hom C E}
         {h₁ : Hom B D}{h₂ : Hom D F}
       → f₂ ∙ g₁ ≡ h₁ ∙ f₁ → f₃ ∙ g₂ ≡ h₂ ∙ f₂
       → f₃ ∙ (g₂ ∙ g₁) ≡ (h₂ ∙ h₁) ∙ f₁
 □-lem {f₁ = f₁} {f₂ = f₂} {f₃ = f₃} {g₁ = g₁} {g₂ = g₂} {h₁ = h₁} {h₂ = h₂} p₁ p₂ =
      proof
         f₃ ∙ (g₂ ∙ g₁)
      ≡⟨ sym ass ⟩
         (f₃ ∙ g₂) ∙ g₁
      ≡⟨ cong (λ k → k ∙ g₁) p₂ ⟩
         (h₂ ∙ f₂) ∙ g₁
      ≡⟨ ass ⟩
         h₂ ∙ (f₂ ∙ g₁)
      ≡⟨ cong (_∙_ h₂) p₁ ⟩
         h₂ ∙ (h₁ ∙ f₁)
      ≡⟨ sym ass ⟩
         (h₂ ∙ h₁) ∙ f₁
      ∎

 _□_ : {A B C D E F : Obj}{f₁ : Hom A B}{f₂ : Hom C D}{f₃ : Hom E F}
     → CommSquare f₂ f₃ → CommSquare f₁ f₂ → CommSquare f₁ f₃
 _□_ {f₁ = f₁} {f₂ = f₂} {f₃ = f₃} (g₂ , h₂ , p₂) (g₁ , h₁ , p₁)
     = g₂ ∙ g₁ , h₂ ∙ h₁ , □-lem p₁ p₂   

 snd₂ : {A : Set}{B : A → Set}{C : (x : A) → B x → Set} → (x : ∃₂ C) → B (fst x)
 snd₂ (x , y , z) = y

 cs-ir : {A B C D : Obj}{f₁ : Hom A B}{f₂ : Hom C D} 
          → (x y : CommSquare f₁ f₂) 
          → fst x ≡ fst y → snd₂ x ≡ snd₂ y
          → x ≡ y
 cs-ir (g₁ , g₂ , p) (.g₁ , .g₂ , q) refl refl rewrite ir p q = refl

module ArrowCat (∁ : Cat) where

 open Cat ∁
 open CommSquare ∁
 
 ArrObj : Set₁
 ArrObj = ∃₂ Hom

 ArrHom : ArrObj → ArrObj → Set
 ArrHom (A , B , f₁) (C , D , f₂) = CommSquare f₁ f₂
 
 ArrId : {X : ArrObj} → ArrHom X X 
 ArrId = iden , iden , trans idr (sym idl)  

 ArrowCat : Cat
 ArrowCat = record {
              Obj = ArrObj
            ; Hom = ArrHom
            ; iden = ArrId
            ; _∙_ = _□_
            ; idl = λ { {f = f} → cs-ir (ArrId □ f) f idl idl }
            ; idr = λ { {f = f } → cs-ir (f □ ArrId) f idr idr}
            ; ass = λ { {f = f} {g = g} {h = h} → cs-ir ((f □ g) □ h) (f □ (g □ h)) ass ass } }
 
--------------------------------------------------
{- Generalizamos la noción de isomorfismo de la clase pasada a cualquier categoría -}

{- Isomorfismo en una categoría -}

open Cat

record Iso {C : Cat}(A B : Obj C)(fun : Hom C A B) : Set where
  constructor iso
  field inv : Hom C B A
        law1 : _∙_ C fun inv  ≡ iden C {B}
        law2 : _∙_ C inv fun  ≡ iden C {A}

--------------------------------------------------

{- Ejercicio
 Mostrar que en el caso de la categoría Sets, isomorfismo corresponde a biyección de funciones

Ayuda : puede ser útil usar cong-app
-}

open import Records-completo using ( Biyectiva )

iso→biyec : {A B : Set}{f : A → B} → Iso {Sets} A B f → Biyectiva f
iso→biyec {f = f} (iso inv law1 law2) y = inv y , cong-app law1 y , 
                                          λ x fx≡y 
                                             →  proof
                                                   inv y
                                                ≡⟨ cong inv (sym fx≡y) ⟩ 
                                                   inv (f x)
                                                ≡⟨ cong-app law2 x ⟩
                                                   x
                                                ∎

biyec→iso : {A B : Set}{f : A → B} → Biyectiva f → Iso {Sets} A B f
biyec→iso {f = f} b = iso  (λ y → fst (b y)) 
                           (ext (fst ∘ snd ∘ b)) 
                           (ext λ x → snd (snd (b (f x))) x refl)

--------------------------------------------------
{- Ejercicio:
 Probar que un isormofismo en (C : Cat) es un isomorfismo en (C Op).

-}

iso-op : {∁ : Cat}{A B : Obj ∁}{f : Hom ∁ A B} → Iso {∁} A B f → Iso {∁ Op} B A f
iso-op (iso inv law1 law2) = iso inv law2 law1 

--------------------------------------------------
{- Ejercicio EXTRA:
 Definir la categoría de pointed sets:
  - objetos son conjuntos junto con un elemento designado del conjunto.
     Por ejemplo (Bool , false), (ℕ , 0) , etc.
  - los morfismos son funciones entre los conjuntos que preservan el punto
     (A,a) → (B, b) es una función f : A → B, tal que f(a) = b 
-}

PSets : Cat
PSets = record {
           Obj = ∃ id
         ; Hom = λ { (A , a) (B , b) → Σ (A → B) λ f → f a ≡ b }
         ; iden = id , refl
         ; _∙_ = λ { (f₂ , p₂) (f₁ , p₁) → f₂ ∘ f₁ , trans (cong f₂ p₁) p₂ }
         ; idl = λ { {f = f , p} → cong (_,_ f) (ir _ p) }
         ; idr = λ { {f = f , p} → cong (_,_ f) (ir _ p) }
         ; ass = λ { {f = f , p} {g = g , q} {h = h , r} 
                     → cong (_,_ (f ∘ g ∘ h)) (ir _ _) } }

--------------------------------------------------

{- Ejercicio EXTRA:
 Definir la categoría cuyos
  - objetos son conjuntos finitos (y por lo tanto isomorfos a Fin n para algún n)
  - morfismos son isomorfismos.  
-}

open import Data.Nat hiding (_⊔_)

SetIso : (A B : Set) → Set
SetIso A B = ∃ (Iso {Sets} A B)    

data Fin : ℕ -> Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n -> Fin (suc n)

Finite : (A : Set) → Set
Finite A = ∃ λ n → SetIso A (Fin n)

open Iso

{- No se como representar Obj -}

FIN : Cat
FIN = record {
              Obj = ∃ Finite
            ; Hom = λ { (A , _) (B , _) → SetIso A B }
            ; iden = id , iso id refl refl
            ; _∙_ = λ {(f , i) (g , j) 
                     → f ∘ g , iso (inv j ∘ inv i) 
                                   (ext λ y → trans 
                                                (cong f (cong-app (law1 j) (inv i y)) )
                                                (cong-app (law1 i) y)) 
                                   (ext λ x → {!   !})}
            ; idl = {!   !}
            ; idr = {!   !}
            ; ass = {!   !} }

--------------------------------------------------


