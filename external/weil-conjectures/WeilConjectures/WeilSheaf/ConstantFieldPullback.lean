/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraCyclicChain
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.Transition
public import WeilConjectures.WeilSheaf.ConstantFieldEquivalence
public import WeilConjectures.WeilSheaf.ConstantTwistCohomology
public import WeilConjectures.WeilSheaf.GeometricFiberPullback

/-!
# Pulled-back Weil sheaves over a smaller base field

Let `k₀ ⊆ k'` be finite fields with `[k' : k₀] = m + 1` and `V` a `k'`-scheme, regarded also as a
`k₀`-scheme. Taking the first piece of the geometric fibre `V ⊗_{k₀} k̄` is an equivalence
`ProEtaleWeilSheaf k₀ l V ≌ ProEtaleWeilSheaf k' l V`
(`AlgebraicGeometry.ProEtaleWeilSheaf.constantFieldFunctor`). This file computes it on the Weil
sheaves pulled back from `V` itself and twisted by a constant: the pullback `p₀^* H` of an
`ℓ`-adic sheaf `H` on `V` with its canonical Weil structure relative to `k₀` multiplied by `b`
goes to the pullback `p'^* H` with its canonical Weil structure relative to `k'` multiplied by
`b^{m+1}`
(`ProEtaleWeilSheaf.constantFieldFunctorObjGeometricFiberPullbackTwistIso`).
Indeed the Frobenius relative to `k'` is the `(m+1)`-st power of the one relative to `k₀`.

## Main definitions

- `AlgebraicGeometry.ProEtale.adicUpperStarFactorIso`: `g₁^* g₂^* M ≅ g^* M` along a
  factorisation `g₁ ≫ g₂ = g`, with its cocycle and congruence laws.
- `AlgebraicGeometry.ProEtaleWeilSheaf.geometricFiberPullbackTwist`: `(p^* H, b • can)`.
- `AlgebraicGeometry.ProEtaleWeilSheaf.constantFieldFunctorObjGeometricFiberPullbackTwistIso`.
-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

noncomputable section

namespace AlgebraicGeometry

namespace ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- The identification `g₁^* g₂^* M ≅ (g₁ ≫ g₂)^* M = g^* M` along a factorisation
`g₁ ≫ g₂ = g`. -/
def adicUpperStarFactorIso {X Y Z : Scheme.{u}} {g₁ : X ⟶ Y} {g₂ : Y ⟶ Z} {g : X ⟶ Z}
    (h : g₁ ≫ g₂ = g) (M : AdicSheaf l Z) :
    (g₁)^*ᵃ[l].obj ((g₂)^*ᵃ[l].obj M) ≅ (g)^*ᵃ[l].obj M :=
  (adicUpperStarComp l g₁ g₂).symm.app M ≪≫ (adicUpperStarCongr l h).app M

lemma adicUpperStarFactorIso_hom {X Y Z : Scheme.{u}} {g₁ : X ⟶ Y} {g₂ : Y ⟶ Z} {g : X ⟶ Z}
    (h : g₁ ≫ g₂ = g) (M : AdicSheaf l Z) :
    (adicUpperStarFactorIso h M).hom =
      (adicUpperStarComp l g₁ g₂).inv.app M ≫ (adicUpperStarCongr l h).hom.app M :=
  rfl

/-- **The cocycle law of the factorisation isomorphisms**: for `b ≫ f = g` and `a ≫ g = h`,
the composite `a^* b^* f^* M ≅ a^* g^* M ≅ h^* M` is `a^* b^* f^* M ≅ (a ≫ b)^* f^* M ≅ h^* M`. -/
@[reassoc]
lemma adicUpperStarFactorIso_map_hom_comp {X Y Z W : Scheme.{u}} (a : X ⟶ Y) {b : Y ⟶ Z}
    {f : Z ⟶ W} {g : Y ⟶ W} {h : X ⟶ W} (hb : b ≫ f = g) (ha : a ≫ g = h)
    (hab : (a ≫ b) ≫ f = h) (M : AdicSheaf l W) :
    (a)^*ᵃ[l].map (adicUpperStarFactorIso hb M).hom ≫ (adicUpperStarFactorIso ha M).hom =
      (adicUpperStarComp l a b).inv.app ((f)^*ᵃ[l].obj M) ≫
        (adicUpperStarFactorIso hab M).hom := by
  subst hb ha
  have h := adicUpperStarComp_hom_app_comp_adicUpperStarComp_hom_app a b f M
  have e₁ : (adicUpperStarFactorIso (rfl : b ≫ f = b ≫ f) M).hom =
      (adicUpperStarComp l b f).inv.app M := by
    simp [adicUpperStarFactorIso, adicUpperStarCongr]
  have e₂ : (adicUpperStarFactorIso (rfl : a ≫ b ≫ f = a ≫ b ≫ f) M).hom =
      (adicUpperStarComp l a (b ≫ f)).inv.app M := by
    simp [adicUpperStarFactorIso, adicUpperStarCongr]
  rw [e₁, e₂, ← cancel_epi ((adicUpperStarComp l (a ≫ b) f).hom.app M ≫
    (adicUpperStarComp l a b).hom.app _)]
  conv_lhs => rw [h]
  simp only [adicUpperStarFactorIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

/-- The factorisation isomorphisms are invariant under congruence of the first morphism. -/
@[reassoc]
lemma adicUpperStarCongr_hom_app_comp_adicUpperStarFactorIso_hom {X Y Z : Scheme.{u}}
    {x y : X ⟶ Y} (p : x = y) {f : Y ⟶ Z} {g : X ⟶ Z} (hx : x ≫ f = g) (hy : y ≫ f = g)
    (M : AdicSheaf l Z) :
    (adicUpperStarCongr l p).hom.app ((f)^*ᵃ[l].obj M) ≫ (adicUpperStarFactorIso hy M).hom =
      (adicUpperStarFactorIso hx M).hom := by
  subst p
  simp [adicUpperStarCongr]

end ProEtale

open ProEtale

namespace WeilCoefficients

variable {l : ℕ} [Fact l.Prime]

/-- Multiplications by `b` and by `bᵏ` compose to the multiplication by `bᵏ⁺¹`. -/
lemma smulIso_hom_comp_smulIso_pow_hom {Z : Scheme.{u}} (b : (PadicAlgCl l)ˣ) (k : ℕ)
    (M : AdicSheaf l Z) :
    (smulIso b M).hom ≫ (smulIso (b ^ k) M).hom = (smulIso (b ^ (k + 1)) M).hom := by
  simp only [smulIso, AdicSheaf.smul_smul]
  congr 2
  simp [pow_succ]
  rfl

/-- Multiplication by `b⁰ = 1` is the identity. -/
lemma smulIso_pow_zero_hom {Z : Scheme.{u}} (b : (PadicAlgCl l)ˣ) (M : AdicSheaf l Z) :
    (smulIso (b ^ 0) M).hom = 𝟙 M := by
  simp only [smulIso, pow_zero, Units.val_one]
  exact AdicSheaf.smul_one M

end WeilCoefficients

namespace ProEtaleWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]

/-- The invariance isomorphism `Fr_X^* p^* H ≅ p^* H`, unfolded. -/
lemma geometricFiberPullbackFrobeniusIso_hom_app {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] (H : AdicSheaf l X) :
    ((geometricFiberPullbackFrobeniusIso k₀ l X).app H).hom =
      (adicUpperStarIsoLowerStarInv l
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso).inv.app _ ≫
        (adicUpperStarFactorIso
          (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj _) H).hom := by
  simp [geometricFiberPullbackFrobeniusIso, adicUpperStarFactorIso]

variable (k₀) in
/-- The canonical Weil structure of `p^* H` multiplied by `b ∈ ℚ̄_ℓˣ`. -/
def geometricFiberPullbackTwistStr (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    (H : AdicSheaf l X) (b : (PadicAlgCl l)ˣ) :
    (WeilSheaf.frobeniusPullback k₀ l X).obj
        (((X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)^*ᵃ[l].obj H) ≅
      ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)^*ᵃ[l].obj H :=
  (geometricFiberPullbackFrobeniusIso k₀ l X).app H ≪≫ WeilCoefficients.smulIso b _

variable (k₀) in
/-- The pullback `p^* H` of an `ℓ`-adic sheaf on `X` to the geometric fibre relative to `k₀`,
with its canonical Weil structure multiplied by `b ∈ ℚ̄_ℓˣ`. -/
abbrev geometricFiberPullbackTwist (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    (H : AdicSheaf l X) (b : (PadicAlgCl l)ˣ) : ProEtaleWeilSheaf k₀ l X :=
  IsoAlgebra.mk _ (geometricFiberPullbackTwistStr k₀ l X H b)

variable {k' : Type u} [Field k'] [Finite k'] [Algebra k₀ k'] {V : Scheme.{u}}
  [V.Over (Spec (CommRingCat.of k₀))] [V.Over (Spec (CommRingCat.of k'))]
  (hc : (V ↘ Spec (CommRingCat.of k')) ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ k')) =
    V ↘ Spec (CommRingCat.of k₀))
  {m : ℕ} (hm : Module.finrank k₀ k' = m + 1)

/-- Every piece of the geometric fibre over `k₀` lies over `V` as the geometric fibre over
`k'`: `jᵢ ≫ p₀ = p'`. -/
lemma pieceMap_comp_geometricFiberProj (i : Fin (m + 1)) :
    pieceMap hc i ≫ (V ↘ Spec (CommRingCat.of k₀)).geometricFiberProj =
      (V ↘ Spec (CommRingCat.of k')).geometricFiberProj := by
  simp [pieceMap]

lemma cyclicDecomposition_J (i : Fin (m + 1)) :
    (cyclicDecomposition l hc hm).J i = (pieceMap hc i)^*ᵃ[l] :=
  rfl

lemma cyclicDecomposition_α (k : Fin m) :
    (cyclicDecomposition l hc hm).α k =
      Functor.isoWhiskerRight (adicUpperStarIsoLowerStarInv l
        (V ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso).symm _ ≪≫
      (adicUpperStarComp l _ _).symm ≪≫ adicUpperStarCongr l (pieceMap_comp_frobenius hc k) :=
  rfl

lemma cyclicDecomposition_β :
    (cyclicDecomposition l hc hm).β =
      Functor.isoWhiskerRight (adicUpperStarIsoLowerStarInv l
        (V ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso).symm _ ≪≫
      (adicUpperStarComp l _ _).symm ≪≫
      adicUpperStarCongr l (pieceMap_last_comp_frobenius hc hm) ≪≫
      adicUpperStarComp l _ _ ≪≫ Functor.isoWhiskerLeft _ (adicUpperStarIsoLowerStarInv l
        (V ↘ Spec (CommRingCat.of k')).geometricGaloisFrobenius.asIso) :=
  rfl

lemma cyclicDecomposition_α_hom_app (k : Fin m) (M : AdicSheaf l
    (V ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    ((cyclicDecomposition l hc hm).α k).hom.app M =
      (pieceMap hc k.castSucc)^*ᵃ[l].map ((adicUpperStarIsoLowerStarInv l
        (V ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso).inv.app M) ≫
        (adicUpperStarComp l (pieceMap hc k.castSucc)
          (V ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom).inv.app M ≫
        (adicUpperStarCongr l (pieceMap_comp_frobenius hc k)).hom.app M :=
  rfl

lemma cyclicDecomposition_β_hom_app (M : AdicSheaf l
    (V ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    (cyclicDecomposition l hc hm).β.hom.app M =
      (pieceMap hc (Fin.last m))^*ᵃ[l].map ((adicUpperStarIsoLowerStarInv l
        (V ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso).inv.app M) ≫
        (adicUpperStarComp l (pieceMap hc (Fin.last m))
          (V ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom).inv.app M ≫
        (adicUpperStarCongr l (pieceMap_last_comp_frobenius hc hm)).hom.app M ≫
        (adicUpperStarComp l (V ↘ Spec (CommRingCat.of k')).geometricGaloisFrobenius.asIso.hom
          (pieceMap hc 0)).hom.app M ≫
        (adicUpperStarIsoLowerStarInv l
          (V ↘ Spec (CommRingCat.of k')).geometricGaloisFrobenius.asIso).hom.app _ := by
  rw [cyclicDecomposition_β]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Iso.symm_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]

/-- The identifications `jᵢ^* p₀^* H ≅ p'^* H` of the pieces of a pulled-back sheaf, multiplied
by `bⁱ`. -/
def pieceGeometricFiberPullbackIso (H : AdicSheaf l V) (b : (PadicAlgCl l)ˣ) (i : Fin (m + 1)) :
    (pieceMap hc i)^*ᵃ[l].obj
        (((V ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)^*ᵃ[l].obj H) ≅
      ((V ↘ Spec (CommRingCat.of k')).geometricFiberProj)^*ᵃ[l].obj H :=
  adicUpperStarFactorIso (pieceMap_comp_geometricFiberProj hc i) H ≪≫
    WeilCoefficients.smulIso (b ^ (i : ℕ)) _

lemma geometricFiberPullbackTwistStr_hom (k₀ : Type u) [Field k₀] [Finite k₀] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))] (H : AdicSheaf l X) (b : (PadicAlgCl l)ˣ) :
    (geometricFiberPullbackTwistStr k₀ l X H b).hom =
      (adicUpperStarIsoLowerStarInv l
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso).inv.app _ ≫
        (adicUpperStarFactorIso
          (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj _) H).hom ≫
        (WeilCoefficients.smulIso b _).hom := by
  rw [geometricFiberPullbackTwistStr, Iso.trans_hom,
    geometricFiberPullbackFrobeniusIso_hom_app, Category.assoc]

/-- Pullback commutes with multiplication by a unit. -/
lemma adicUpperStar_map_smulIso_hom {Z₁ Z₂ : Scheme.{u}} (g : Z₁ ⟶ Z₂) (b : (PadicAlgCl l)ˣ)
    (M : AdicSheaf l Z₂) :
    (g)^*ᵃ[l].map (WeilCoefficients.smulIso b M).hom =
      (WeilCoefficients.smulIso b ((g)^*ᵃ[l].obj M)).hom :=
  AdicSheaf.adicUpperStar_map_smul g _ M

/-- Multiplication by a unit is natural. -/
@[reassoc]
lemma smulIso_hom_comp {Z : Scheme.{u}} (b : (PadicAlgCl l)ˣ) {M N : AdicSheaf l Z}
    (f : M ⟶ N) :
    (WeilCoefficients.smulIso b M).hom ≫ f = f ≫ (WeilCoefficients.smulIso b N).hom :=
  AdicSheaf.smul_comp _ f

/-- The identifications of the pieces are compatible with the Weil structure and the `αₖ`. -/
lemma pieceGeometricFiberPullbackIso_compat (H : AdicSheaf l V) (b : (PadicAlgCl l)ˣ)
    (k : Fin m) :
    (pieceMap hc k.castSucc)^*ᵃ[l].map
        (geometricFiberPullbackTwistStr k₀ l V H b).hom ≫
        (pieceGeometricFiberPullbackIso l hc H b k.castSucc).hom =
      ((cyclicDecomposition l hc hm).α k).hom.app
          (((V ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)^*ᵃ[l].obj H) ≫
        (pieceGeometricFiberPullbackIso l hc H b k.succ).hom := by
  rw [cyclicDecomposition_α_hom_app, geometricFiberPullbackTwistStr_hom]
  simp only [pieceGeometricFiberPullbackIso, Iso.trans_hom, Functor.map_comp, Category.assoc,
    adicUpperStar_map_smulIso_hom]
  rw [smulIso_hom_comp_assoc (b := b) (f := (adicUpperStarFactorIso _ H).hom),
    WeilCoefficients.smulIso_hom_comp_smulIso_pow_hom, Fin.val_castSucc, Fin.val_succ]
  refine congrArg ((pieceMap hc k.castSucc)^*ᵃ[l].map _ ≫ ·) ?_
  rw [adicUpperStarFactorIso_map_hom_comp_assoc _ _ _
      (by rw [Category.assoc, Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj,
        pieceMap_comp_geometricFiberProj]),
    adicUpperStarCongr_hom_app_comp_adicUpperStarFactorIso_hom_assoc]

/-- The identification of the last piece is compatible with the Weil structures and `β`. -/
lemma pieceGeometricFiberPullbackIso_compat_last (H : AdicSheaf l V) (b : (PadicAlgCl l)ˣ) :
    (pieceMap hc (Fin.last m))^*ᵃ[l].map (geometricFiberPullbackTwistStr k₀ l V H b).hom ≫
        (pieceGeometricFiberPullbackIso l hc H b (Fin.last m)).hom =
      (cyclicDecomposition l hc hm).β.hom.app
          (((V ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)^*ᵃ[l].obj H) ≫
        (WeilSheaf.frobeniusPullback k' l V).map
          (pieceGeometricFiberPullbackIso l hc H b 0).hom ≫
        (geometricFiberPullbackTwistStr k' l V H (b ^ (m + 1))).hom := by
  rw [cyclicDecomposition_β_hom_app, geometricFiberPullbackTwistStr_hom,
    geometricFiberPullbackTwistStr_hom]
  simp only [pieceGeometricFiberPullbackIso, Iso.trans_hom, Functor.map_comp, Category.assoc,
    adicUpperStar_map_smulIso_hom, Fin.val_zero, WeilCoefficients.smulIso_pow_zero_hom,
    CategoryTheory.Functor.map_id, Category.id_comp]
  refine congrArg ((pieceMap hc (Fin.last m))^*ᵃ[l].map _ ≫ ·) ?_
  rw [smulIso_hom_comp_assoc (b := b) (f := (adicUpperStarFactorIso _ H).hom),
    WeilCoefficients.smulIso_hom_comp_smulIso_pow_hom, Fin.val_last,
    adicUpperStarFactorIso_map_hom_comp_assoc _ _ _
      (by rw [Category.assoc, Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj,
        pieceMap_comp_geometricFiberProj]),
    ← (adicUpperStarIsoLowerStarInv l _).hom.naturality_assoc, Iso.hom_inv_id_app_assoc,
    adicUpperStarFactorIso_map_hom_comp_assoc _ _ _
      (by rw [Category.assoc, pieceMap_comp_geometricFiberProj,
        Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj]),
    Iso.hom_inv_id_app_assoc, adicUpperStarCongr_hom_app_comp_adicUpperStarFactorIso_hom_assoc]

/-- **Pulled-back Weil sheaves over a smaller base field**: the first piece of
`(p₀^* H, b • can₀)` is `(p'^* H, b^{m+1} • can')`. -/
def constantFieldFunctorObjGeometricFiberPullbackTwistIso (H : AdicSheaf l V)
    (b : (PadicAlgCl l)ˣ) :
    (constantFieldFunctor l hc hm).obj (geometricFiberPullbackTwist k₀ l V H b) ≅
      geometricFiberPullbackTwist k' l V H (b ^ (m + 1)) :=
  (cyclicDecomposition l hc hm).functorObjMkIsoMk _ (geometricFiberPullbackTwistStr k₀ l V H b)
    (pieceGeometricFiberPullbackIso l hc H b)
    (pieceGeometricFiberPullbackIso_compat l hc hm H b)
    (geometricFiberPullbackTwistStr k' l V H (b ^ (m + 1)))
    (pieceGeometricFiberPullbackIso_compat_last l hc hm H b)

end ProEtaleWeilSheaf

end AlgebraicGeometry
