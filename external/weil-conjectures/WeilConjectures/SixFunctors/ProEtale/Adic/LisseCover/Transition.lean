/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.Abelian
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantSheafTransport
public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetCoherence

/-!
# Transition matrices of trivialisations of `ℓ`-adic sheaves

Let `G` be an `ℓ`-adic sheaf on `Y`, `h : W ⟶ Y` and `ε : h^* G ≅ ℚ̄_ℓ,Wⁿ` a trivialisation.
For two morphisms `a b : P ⟶ W` with `a ≫ h = b ≫ h`, the two trivialisations of
`(a ≫ h)^* G = (b ≫ h)^* G` obtained by pulling back `ε` along `a` and along `b`
(`AlgebraicGeometry.ProEtale.AdicSheaf.trivPull`) differ by an automorphism of `ℚ̄_ℓ,Pⁿ`, the
*transition morphism* (`AlgebraicGeometry.ProEtale.AdicSheaf.transitionHom`), whose matrix of
locally finite functions is the *transition matrix*
(`AlgebraicGeometry.ProEtale.AdicSheaf.transitionMatrix`). Transition matrices

* are the identity for `a = b` (`transitionMatrix_self`) and multiply along `a, b, c`
  (`transitionMatrix_trans`);
* are compatible with precomposition by a weakly étale `c : Q ⟶ P`
  (`transitionMatrix_comp`): the transition matrix of `c ≫ a, c ≫ b` is that of `a, b`
  composed with `c`;
* are compatible with base change (`transitionMatrix_baseChange`): for `π : T ⟶ Y`, the
  trivialisation of `π^* G` over `W' ⟶ T` induced by `q : W' ⟶ W` has the transition matrices
  of `ε` along `a ≫ q, b ≫ q`.

For the projections of `W ×_Y W` these are the descent data of the trivialisation, and the
compatibilities give the cocycle condition on `W ×_Y W ×_Y W`. The proofs rest on the coherence
of the composition isomorphisms of pullbacks (associativity, and compatibility with the
canonical isomorphisms `g^* ℚ̄_ℓ ≅ ℚ̄_ℓ`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

section Coherence

variable {Q P W Y : Scheme.{u}}

/-- The associativity law for the composition isomorphisms of `ℓ`-adic pullbacks. -/
lemma adicUpperStarComp_hom_app_comp_adicUpperStarComp_hom_app (f : Q ⟶ P) (g : P ⟶ W)
    (h : W ⟶ Y) (M : AdicSheaf l Y) :
    (adicUpperStarComp l (f ≫ g) h).hom.app M ≫
        (adicUpperStarComp l f g).hom.app ((h)^*ᵃ[l].obj M) =
      (adicUpperStarCongr l (Category.assoc f g h)).hom.app M ≫
        (adicUpperStarComp l f (g ≫ h)).hom.app M ≫
          (f)^*ᵃ[l].map ((adicUpperStarComp l g h).hom.app M) := by
  apply Mod.hom_ext
  simp only [Mod.comp_hom', adicUpperStarComp_hom_app_hom, adicUpperStarCongr_hom_app_hom,
    adicUpperStar_map_hom]
  exact upperStarComp_hom_app_comp_upperStarComp_hom_app _ f g h M.X

/-- **Cocycle condition** for the isomorphisms `g^* ℚ̄_ℓ ≅ ℚ̄_ℓ`. -/
lemma adicUpperStarUnitIso_comp (c : Q ⟶ P) (a : P ⟶ W) :
    (adicUpperStarComp l c a).hom.app (AdicSheaf.unit l W) ≫
        (c)^*ᵃ[l].map (adicUpperStarUnitIso l a).hom ≫ (adicUpperStarUnitIso l c).hom =
      (adicUpperStarUnitIso l (c ≫ a)).hom := by
  apply Mod.hom_ext
  simp only [Mod.comp_hom', adicUpperStarComp_hom_app_hom, adicUpperStar_map_hom]
  exact upperStarAdicConstantSheafHom_comp l c a

variable {ι : Type} [Fintype ι]

/-- The components of the isomorphism `g^* ℚ̄_ℓⁿ ≅ ℚ̄_ℓⁿ`. -/
lemma freeUpperStarIso_hom_π (g : P ⟶ W) (i : ι) :
    (AdicSheaf.freeUpperStarIso l ι g).hom ≫ biproduct.π (fun _ : ι ↦ AdicSheaf.unit l P) i =
      (g)^*ᵃ[l].map (biproduct.π (fun _ : ι ↦ AdicSheaf.unit l W) i) ≫
        (adicUpperStarUnitIso l g).hom := by
  simp [AdicSheaf.freeUpperStarIso]

/-- **Cocycle condition** for the isomorphisms `g^* ℚ̄_ℓⁿ ≅ ℚ̄_ℓⁿ`. -/
lemma freeUpperStarIso_comp (c : Q ⟶ P) (a : P ⟶ W) :
    (AdicSheaf.freeUpperStarIso l ι (c ≫ a)).hom =
      (adicUpperStarComp l c a).hom.app _ ≫ (c)^*ᵃ[l].map (AdicSheaf.freeUpperStarIso l ι a).hom ≫
        (AdicSheaf.freeUpperStarIso l ι c).hom := by
  refine biproduct.hom_ext _ _ fun i ↦ ?_
  have := (adicUpperStarComp l c a).hom.naturality
    (biproduct.π (fun _ : ι ↦ AdicSheaf.unit l W) i)
  simp only [Functor.comp_map] at this
  rw [Category.assoc, Category.assoc, freeUpperStarIso_hom_π, freeUpperStarIso_hom_π,
    ← Functor.map_comp_assoc, freeUpperStarIso_hom_π, Functor.map_comp_assoc,
    ← reassoc_of% this, adicUpperStarUnitIso_comp]

end Coherence

namespace AdicSheaf

variable {Y W P Q : Scheme.{u}} {G : AdicSheaf l Y} {h : W ⟶ Y} {n : ℕ}
  (ε : (h)^*ᵃ[l].obj G ≅ ⨁ fun _ : Fin n ↦ unit l W)

/-- Pulling back a trivialisation along a composite. -/
lemma trivPull_comp_hom (c : Q ⟶ P) (a : P ⟶ W) :
    (trivPull h ε (c ≫ a)).hom = (adicUpperStarCongr l (Category.assoc c a h)).hom.app G ≫
      (adicUpperStarComp l c (a ≫ h)).hom.app G ≫ (c)^*ᵃ[l].map (trivPull h ε a).hom ≫
        (freeUpperStarIso l (Fin n) c).hom := by
  have h₁ := (adicUpperStarComp l c a).hom.naturality ε.hom
  simp only [Functor.comp_map] at h₁
  have h₂ := adicUpperStarComp_hom_app_comp_adicUpperStarComp_hom_app c a h G
  rw [trivPull, trivPull, Iso.trans_hom, Iso.trans_hom, Iso.trans_hom, Iso.trans_hom,
    Iso.app_hom, Iso.app_hom, Functor.mapIso_hom, Functor.mapIso_hom, freeUpperStarIso_comp,
    reassoc_of% h₁, reassoc_of% h₂]
  simp only [Functor.map_comp, Category.assoc]

/-- The congruence isomorphisms compose. The composite equality is an independent hypothesis,
so that no new equality proofs are built: comparing proofs of equalities of morphisms of schemes
up to different instance paths can make the kernel time out. -/
@[reassoc]
lemma adicUpperStarCongr_hom_app_trans {X Z : Scheme.{u}} {x y z : X ⟶ Z} (p : x = y) (p' : y = z)
    (p'' : x = z)
    (M : AdicSheaf l Z) :
    (adicUpperStarCongr l p).hom.app M ≫ (adicUpperStarCongr l p').hom.app M =
      (adicUpperStarCongr l p'').hom.app M := by
  subst p p'
  simp [adicUpperStarCongr]

/-- The inverse of a congruence isomorphism is a congruence isomorphism. -/
lemma adicUpperStarCongr_inv_app {X Z : Scheme.{u}} {x y : X ⟶ Z} (p : x = y) (q : y = x)
    (M : AdicSheaf l Z) :
    (adicUpperStarCongr l p).inv.app M = (adicUpperStarCongr l q).hom.app M := by
  subst p
  simp [adicUpperStarCongr]

/-- The pullback of a congruence isomorphism is a congruence isomorphism. -/
lemma adicUpperStarComp_inv_app_comp_congr_comp_hom_app {X Z : Scheme.{u}} (c : Q ⟶ X) {x y : X ⟶ Z}
    (p : x = y) (p' : c ≫ x = c ≫ y) (M : AdicSheaf l Z) :
    (adicUpperStarComp l c x).inv.app M ≫ (adicUpperStarCongr l p').hom.app M ≫
        (adicUpperStarComp l c y).hom.app M =
      (c)^*ᵃ[l].map ((adicUpperStarCongr l p).hom.app M) := by
  subst p
  simp [adicUpperStarCongr]

/-- The composition isomorphisms are compatible with congruences of the first morphism. -/
lemma adicUpperStarComp_hom_app_comp_congr {X Z Z' : Scheme.{u}} {x y : X ⟶ Z'} (z : Z' ⟶ Z)
    (p : x = y) (p' : x ≫ z = y ≫ z) (M : AdicSheaf l Z) :
    (adicUpperStarComp l x z).hom.app M ≫ (adicUpperStarCongr l p).hom.app ((z)^*ᵃ[l].obj M) =
      (adicUpperStarCongr l p').hom.app M ≫ (adicUpperStarComp l y z).hom.app M := by
  subst p
  simp [adicUpperStarCongr]

/-- The *transition morphism* of a trivialisation `ε : h^* G ≅ ℚ̄_ℓⁿ` at two morphisms
`a b : P ⟶ W` with `a ≫ h = b ≫ h`: the pullback of `ε` along `a`, inverted, followed by the
pullback along `b`. -/
noncomputable def transitionHom (a b : P ⟶ W) (hab : a ≫ h = b ≫ h) :
    (⨁ fun _ : Fin n ↦ unit l P) ⟶ ⨁ fun _ : Fin n ↦ unit l P :=
  (trivPull h ε a).inv ≫ (adicUpperStarCongr l hab).hom.app G ≫ (trivPull h ε b).hom

/-- The defining formula of the transition morphism. -/
lemma transitionHom_eq (a b : P ⟶ W) (hab : a ≫ h = b ≫ h) :
    (transitionHom ε a b hab) =
      (trivPull h ε a).inv ≫ (adicUpperStarCongr l hab).hom.app G ≫ (trivPull h ε b).hom :=
  rfl

/-- The transition morphism of a morphism with itself is the identity. -/
lemma transitionHom_self (a : P ⟶ W) (haa : a ≫ h = a ≫ h) :
    (transitionHom ε a a haa) = 𝟙 _ := by
  rw [transitionHom_eq]
  simp [adicUpperStarCongr]

/-- Transition morphisms compose. -/
lemma transitionHom_trans (a b c : P ⟶ W) (hab : a ≫ h = b ≫ h) (hbc : b ≫ h = c ≫ h)
    (hac : a ≫ h = c ≫ h) :
    (transitionHom ε a b hab) ≫ (transitionHom ε b c hbc) =
      (transitionHom ε a c hac) := by
  rw [transitionHom_eq, transitionHom_eq, transitionHom_eq, Category.assoc, Category.assoc,
    Iso.hom_inv_id_assoc, adicUpperStarCongr_hom_app_trans_assoc hab hbc hac]


/-- The transition morphism at `c ≫ a, c ≫ b` is the pullback along `c` of the transition
morphism at `a, b`. -/
lemma transitionHom_comp (c : Q ⟶ P) (a b : P ⟶ W) (hab : a ≫ h = b ≫ h)
    (hab' : (c ≫ a) ≫ h = (c ≫ b) ≫ h) :
    (transitionHom ε (c ≫ a) (c ≫ b) hab') = (freeUpperStarIso l (Fin n) c).inv ≫
      (c)^*ᵃ[l].map (transitionHom ε a b hab) ≫ (freeUpperStarIso l (Fin n) c).hom := by
  have hinv : (trivPull h ε (c ≫ a)).inv = (freeUpperStarIso l (Fin n) c).inv ≫
      (c)^*ᵃ[l].map (trivPull h ε a).inv ≫ (adicUpperStarComp l c (a ≫ h)).inv.app G ≫
        (adicUpperStarCongr l (Category.assoc c a h).symm).hom.app G := by
    rw [← cancel_epi (trivPull h ε (c ≫ a)).hom, Iso.hom_inv_id, trivPull_comp_hom]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc,
      Iso.hom_inv_id]
    simp [adicUpperStarCongr]
  rw [transitionHom_eq, transitionHom_eq, hinv, trivPull_comp_hom, Functor.map_comp,
    Functor.map_comp]
  simp only [Category.assoc]
  congr 2
  rw [adicUpperStarCongr_hom_app_trans_assoc _ _ (show c ≫ a ≫ h = (c ≫ b) ≫ h by simp [hab]),
    adicUpperStarCongr_hom_app_trans_assoc _ _ (show c ≫ a ≫ h = c ≫ b ≫ h by simp [hab]),
    ← reassoc_of% adicUpperStarComp_inv_app_comp_congr_comp_hom_app c hab]

variable {T W' : Scheme.{u}} (π : T ⟶ Y) (hT : W' ⟶ T) (q : W' ⟶ W) (hq : hT ≫ π = q ≫ h)

/-- The base change of a trivialisation `ε : h^* G ≅ ℚ̄_ℓⁿ` along `π : T ⟶ Y`: for `W' ⟶ T`
with a morphism `q : W' ⟶ W` over `π`, the trivialisation `hT^* π^* G ≅ (q ≫ h)^* G ≅ ℚ̄_ℓⁿ`. -/
noncomputable def trivBaseChange :
    (hT)^*ᵃ[l].obj ((π)^*ᵃ[l].obj G) ≅ ⨁ fun _ : Fin n ↦ unit l W' :=
  ((adicUpperStarComp l hT π).app G).symm ≪≫ (adicUpperStarCongr l hq).app G ≪≫
    trivPull h ε q


/-- The pullbacks of the base-changed trivialisation are the pullbacks of `ε`. -/
lemma trivPull_trivBaseChange_hom (a : P ⟶ W') (p : (a ≫ hT) ≫ π = (a ≫ q) ≫ h) :
    (trivPull hT (trivBaseChange ε π hT q hq) a).hom =
      (adicUpperStarComp l (a ≫ hT) π).inv.app G ≫ (adicUpperStarCongr l p).hom.app G ≫
        (trivPull h ε (a ≫ q)).hom := by
  have h₂ := adicUpperStarComp_hom_app_comp_adicUpperStarComp_hom_app a hT π G
  have h₃ := adicUpperStarComp_inv_app_comp_congr_comp_hom_app (M := G) a hq (by simp [hq])
  rw [trivPull_comp_hom, ← cancel_epi ((adicUpperStarComp l (a ≫ hT) π).hom.app G),
    Iso.hom_inv_id_app_assoc, trivPull, trivBaseChange]
  rw [Iso.trans_hom, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.trans_hom,
    Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  have hc : (a)^*ᵃ[l].map ((adicUpperStarComp l hT π).hom.app G) ≫
      (a)^*ᵃ[l].map ((adicUpperStarComp l hT π).inv.app G) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  rw [reassoc_of% h₂, reassoc_of% hc, ← reassoc_of% h₃,
    Iso.hom_inv_id_app_assoc,
    adicUpperStarCongr_hom_app_trans_assoc _ _ (show (a ≫ hT) ≫ π = a ≫ q ≫ h by simp [hq]),
    adicUpperStarCongr_hom_app_trans_assoc _ _ (show (a ≫ hT) ≫ π = a ≫ q ≫ h by simp [hq])]

/-- Transition morphisms are compatible with base change. -/
lemma transitionHom_baseChange (a b : P ⟶ W') (hab : a ≫ hT = b ≫ hT)
    (hab' : (a ≫ q) ≫ h = (b ≫ q) ≫ h) :
    transitionHom (trivBaseChange ε π hT q hq) a b hab = transitionHom ε (a ≫ q) (b ≫ q) hab' := by
  have pa : (a ≫ hT) ≫ π = (a ≫ q) ≫ h := by simp [hq]
  have pb : (b ≫ hT) ≫ π = (b ≫ q) ≫ h := by simp [hq]
  have hinv : (trivPull hT (trivBaseChange ε π hT q hq) a).inv =
      (trivPull h ε (a ≫ q)).inv ≫ (adicUpperStarCongr l pa).inv.app G ≫
        (adicUpperStarComp l (a ≫ hT) π).hom.app G := by
    rw [← cancel_epi (trivPull hT (trivBaseChange ε π hT q hq) a).hom, Iso.hom_inv_id,
      trivPull_trivBaseChange_hom ε π hT q hq a pa]
    simp only [Category.assoc]
    rw [Iso.hom_inv_id_assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app]
    rfl
  have hc := adicUpperStarComp_hom_app_comp_congr π hab (by simp [hab]) G
  rw [transitionHom_eq, transitionHom_eq, hinv, trivPull_trivBaseChange_hom ε π hT q hq b pb]
  simp only [Category.assoc]
  rw [reassoc_of% hc, Iso.hom_inv_id_app_assoc,
    adicUpperStarCongr_inv_app pa pa.symm,
    adicUpperStarCongr_hom_app_trans_assoc _ _ (show (a ≫ q) ≫ h = (b ≫ hT) ≫ π by
      simp only [Category.assoc, hq] at hab' ⊢; exact hab'),
    adicUpperStarCongr_hom_app_trans_assoc _ _ hab']

/-- Pulling back a trivialisation followed by an automorphism of `ℚ̄_ℓⁿ`. -/
lemma trivPull_trans_hom (A : (⨁ fun _ : Fin n ↦ unit l W) ≅ ⨁ fun _ : Fin n ↦ unit l W)
    (a : P ⟶ W) :
    (trivPull h (ε ≪≫ A) a).hom = (trivPull h ε a).hom ≫ (freeUpperStarIso l (Fin n) a).inv ≫
      (a)^*ᵃ[l].map A.hom ≫ (freeUpperStarIso l (Fin n) a).hom := by
  rw [trivPull, trivPull, Iso.trans_hom, Iso.trans_hom, Iso.trans_hom, Iso.trans_hom,
    Functor.mapIso_hom, Functor.mapIso_hom, Iso.trans_hom, Functor.map_comp]
  simp only [Category.assoc]
  rw [Iso.hom_inv_id_assoc]

/-- Changing a trivialisation by an automorphism `A` of `ℚ̄_ℓⁿ` conjugates its transition
morphisms by the pullbacks of `A`. -/
lemma transitionHom_trans_iso (A : (⨁ fun _ : Fin n ↦ unit l W) ≅ ⨁ fun _ : Fin n ↦ unit l W)
    (a b : P ⟶ W) (hab : a ≫ h = b ≫ h) :
    transitionHom (ε ≪≫ A) a b hab = ((freeUpperStarIso l (Fin n) a).inv ≫
      (a)^*ᵃ[l].map A.inv ≫ (freeUpperStarIso l (Fin n) a).hom) ≫ transitionHom ε a b hab ≫
        ((freeUpperStarIso l (Fin n) b).inv ≫ (b)^*ᵃ[l].map A.hom ≫
          (freeUpperStarIso l (Fin n) b).hom) := by
  have hinv : (trivPull h (ε ≪≫ A) a).inv = (freeUpperStarIso l (Fin n) a).inv ≫
      (a)^*ᵃ[l].map A.inv ≫ (freeUpperStarIso l (Fin n) a).hom ≫ (trivPull h ε a).inv := by
    rw [← cancel_epi (trivPull h (ε ≪≫ A) a).hom, Iso.hom_inv_id, trivPull_trans_hom]
    simp only [Category.assoc]
    rw [Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_assoc, Iso.hom_inv_id]
  rw [transitionHom_eq, transitionHom_eq, hinv, trivPull_trans_hom]
  simp only [Category.assoc]

/-- The *transition matrix* of a trivialisation `ε : h^* G ≅ ℚ̄_ℓⁿ` at two morphisms
`a b : P ⟶ W` with `a ≫ h = b ≫ h`: the matrix of locally finite functions of the transition
morphism. -/
noncomputable def transitionMatrix (a b : P ⟶ W) (hab : a ≫ h = b ≫ h) :
    Matrix (Fin n) (Fin n) (PadicAlgCl.locallyFiniteFunctions l P) :=
  unitMatrix (transitionHom ε a b hab)

/-- The transition matrix of a morphism with itself is the identity. -/
lemma transitionMatrix_self (a : P ⟶ W) (haa : a ≫ h = a ≫ h) :
    transitionMatrix ε a a haa = 1 := by
  rw [transitionMatrix, transitionHom_self, unitMatrix_id]

/-- **Cocycle condition**: transition matrices multiply. -/
lemma transitionMatrix_trans (a b c : P ⟶ W) (hab : a ≫ h = b ≫ h) (hbc : b ≫ h = c ≫ h)
    (hac : a ≫ h = c ≫ h) :
    transitionMatrix ε a c hac = transitionMatrix ε b c hbc * transitionMatrix ε a b hab := by
  rw [transitionMatrix, transitionMatrix, transitionMatrix,
    ← transitionHom_trans ε a b c hab hbc hac,
    unitMatrix_comp]

/-- **Transition matrices are compatible with precomposition** by a weakly étale morphism. -/
lemma transitionMatrix_comp (c : Q ⟶ P) [WeaklyEtale c] (a b : P ⟶ W) (hab : a ≫ h = b ≫ h)
    (hab' : (c ≫ a) ≫ h = (c ≫ b) ≫ h) :
    transitionMatrix ε (c ≫ a) (c ≫ b) hab' =
      (transitionMatrix ε a b hab).map (PadicAlgCl.locallyFiniteFunctionsComp l c.base.hom) := by
  rw [transitionMatrix, transitionMatrix, transitionHom_comp ε c a b hab hab',
    ← unitMatrix_adicUpperStar]

/-- Transition matrices only depend on the morphisms. -/
lemma transitionMatrix_congr {a a' b b' : P ⟶ W} (ha : a = a') (hb : b = b')
    (hab : a ≫ h = b ≫ h) (hab' : a' ≫ h = b' ≫ h) :
    transitionMatrix ε a b hab = transitionMatrix ε a' b' hab' := by
  subst ha hb
  rfl

/-- **Transition matrices are compatible with base change.** -/
lemma transitionMatrix_baseChange (a b : P ⟶ W') (hab : a ≫ hT = b ≫ hT)
    (hab' : (a ≫ q) ≫ h = (b ≫ q) ≫ h) :
    transitionMatrix (trivBaseChange ε π hT q hq) a b hab =
      transitionMatrix ε (a ≫ q) (b ≫ q) hab' := by
  rw [transitionMatrix, transitionMatrix, transitionHom_baseChange]

/-- Changing a trivialisation by an automorphism `A` of `ℚ̄_ℓⁿ` with matrix `M` changes its
transition matrices at `a, b` to `M(b) T M(a)⁻¹`. -/
lemma transitionMatrix_trans_iso
    (A : (⨁ fun _ : Fin n ↦ unit l W) ≅ ⨁ fun _ : Fin n ↦ unit l W)
    (a b : P ⟶ W) [WeaklyEtale a] [WeaklyEtale b] (hab : a ≫ h = b ≫ h) :
    transitionMatrix (ε ≪≫ A) a b hab =
      (unitMatrix A.hom).map (PadicAlgCl.locallyFiniteFunctionsComp l b.base.hom) *
        transitionMatrix ε a b hab *
          (unitMatrix A.inv).map (PadicAlgCl.locallyFiniteFunctionsComp l a.base.hom) := by
  rw [transitionMatrix, transitionMatrix, transitionHom_trans_iso, unitMatrix_comp,
    unitMatrix_comp, unitMatrix_adicUpperStar, unitMatrix_adicUpperStar, mul_assoc]

end AdicSheaf

end AlgebraicGeometry.ProEtale
