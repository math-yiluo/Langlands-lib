/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius.ConstantExtension
public import WeilConjectures.WeilSheaf.FrobeniusTwistSubobject
public import WeilConjectures.WeilSheaf.UpperStarExact
public import WeilConjectures.WeilSheaf.StalkComparison
public import WeilConjectures.WeilSheaf.EquivariantPullbackExchange

/-!
# Pulling Weil sheaves back to a scheme over a finite extension

Let `k₀ ⊆ L` be finite fields, `[L : k₀] = N`, let `X₀` be a `k₀`-scheme with geometric fiber `X̄`
and geometric Galois Frobenius `Fr`, and let `Y` be an `L`-scheme with geometric fiber `Ȳ` and
geometric Galois Frobenius `Fr_Y`. A morphism `j : Ȳ ⟶ X̄` with `j ≫ Fr^N = Fr_Y ≫ j` (for
instance the base change of an `L`-scheme `Y ⊆ X₀ ⊗ L`, such as a curve defined over `L`) carries
a Weil sheaf `F` on `X₀`, through the iterated Weil structure `φ_N : (Fr^N)^* F̄ ≅ F̄`, to a Weil
sheaf on `Y` over `L` with underlying sheaf `j^* F̄`
(`AlgebraicGeometry.WeilSheaf.curvePullback`). The same applies to a subsheaf `P ⊆ F̄` which is
only defined over `L`, i.e. fixed by the `N`-th iterate of the Frobenius twist
(`AlgebraicGeometry.WeilSheaf.curvePullbackSub`).

This is how the blueprint restricts a Weil sheaf and its geometric constituents to a curve which is
only defined over a finite constant extension (`theorem-real-constructible-sheaves-are-mixed--1`,
`corollary-curve-preserving-geometric-irreducibility--1`). The stalks of the pullback are compared
in `WeilConjectures.WeilSheaf.EquivariantPullback`.

## Main definitions

- `AlgebraicGeometry.WeilSheaf.curvePullback`: the pullback `WeilSheaf k₀ l X₀ ⥤ WeilSheaf L l Y`.
- `AlgebraicGeometry.WeilSheaf.curvePullbackSub`: the pullback of a subsheaf defined over `L`.
-/

@[expose] public section

-- The Weil sheaf stalks and the `ℓ`-adic pullbacks used here are elaborated without these
-- instances; elaborating the statements through them would produce terms which the kernel
-- compares slowly with the imported ones.
attribute [-instance] ModuleCat.instIsRightAdjointForgetLinearMapIdCarrier
  ModuleCat.isGrothendieckAbelian_of_commRing
  CategoryTheory.hasGlobalSectionsFunctor_of_hasLimitsOfShape

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

open ProEtale

variable {l : ℕ} [Fact l.Prime]

namespace WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  {L : Type u} [Field L] [Finite L] [Fact (ringChar L ≠ l)]
  {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of L))] {N : ℕ}
  (j : (Y ↘ Spec (CommRingCat.of L)).geometricFiber ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  (hj : j ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).asIso.hom =
    (Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius.asIso.hom ≫ j)

/-- The pullback of Weil sheaves along `j : Ȳ ⟶ X̄` with `j ≫ Fr^N = Fr_Y ≫ j`: the pullback
`j^* F̄` with the Weil structure induced by the iterated Weil structure `φ_N` of `F`. -/
noncomputable def curvePullback : WeilSheaf k₀ l X ⥤ WeilSheaf L l Y where
  obj F := ⟨(ProEtaleWeilSheaf.equivariantPullback _ j hj).obj (F.powIsoAlgebra N),
    F.isAdicConstructibleSheaf_carrier.upperStar j⟩
  -- The morphism of algebras is built between `IsoAlgebra.mk` and `Algebra.mk` objects, which the
  -- kernel matches with `F.powIsoAlgebra N` by unfolding it; against `F.obj`, which has the same
  -- carrier but is an algebra for another functor, the comparison is slow.
  map {F G} φ := ObjectProperty.homMk ((ProEtaleWeilSheaf.equivariantPullback _ j hj).map
    (ObjectProperty.homMk (X := IsoAlgebra.mk _ (F.frobeniusPowIso N))
      (Y := IsoAlgebra.mk _ (G.frobeniusPowIso N))
      (⟨φ.hom.hom.f, frobeniusPowIso_hom_naturality φ N⟩ :
        Algebra.Hom ⟨_, (F.frobeniusPowIso N).hom⟩ ⟨_, (G.frobeniusPowIso N).hom⟩)))
  map_id _ := ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _
    (Algebra.Hom.ext ((j)^*ᵃ[l].map_id _)))
  map_comp _ _ := ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _
    (Algebra.Hom.ext ((j)^*ᵃ[l].map_comp _ _)))


lemma curvePullback_obj (F : WeilSheaf k₀ l X) :
    (curvePullback j hj).obj F = ⟨(ProEtaleWeilSheaf.equivariantPullback _ j hj).obj
      (F.powIsoAlgebra N), F.isAdicConstructibleSheaf_carrier.upperStar j⟩ :=
  rfl
@[simp]
lemma curvePullback_obj_obj_carrier (F : WeilSheaf k₀ l X) :
    ((curvePullback j hj).obj F).obj.carrier = (j)^*ᵃ[l].obj F.obj.carrier :=
  rfl

/-- The Weil structure of the curve pullback is transported from the iterated Weil structure. -/
lemma curvePullback_obj_obj_obj_str (F : WeilSheaf k₀ l X) :
    ((curvePullback j hj).obj F).obj.obj.str =
      (adicUpperStarCompFrobeniusIsoOfComm _ j hj).hom.app (F.powIsoAlgebra N).carrier ≫
        (j)^*ᵃ[l].map (F.powIsoAlgebra N).obj.str :=
  IsoAlgebra.mapOfNatIso_obj_obj_str _ _


-- Stated for an arbitrary isomorphism `α` and specialised to
-- `ProEtale.upperStarIsoLowerStarInv` below: comparing two components of the concrete
-- `upperStarIsoLowerStarInv` at objects which are only definitionally equal makes the kernel unfold
-- the isomorphism (about 30s), while for a variable `α` it only compares the objects.
private lemma hom_app_comp_forget_map_frobeniusPowIso (F : WeilSheaf k₀ l X) (M : ℕ)
    (α : (((X ↘ Spec
        (CommRingCat.of k₀)).geometricGaloisFrobenius ^ M).asIso.hom)^*[WeilCoefficients l] ≅
      (((X ↘ Spec
        (CommRingCat.of k₀)).geometricGaloisFrobenius ^ M).asIso.inv)_*[WeilCoefficients l]) :
    α.hom.app F.obj.carrier.X ≫ (ProEtale.AdicSheaf.forget _).map (F.frobeniusPowIso M).hom =
      α.hom.app (F.powIsoAlgebra M).carrier.X ≫
        (ProEtale.AdicSheaf.forget _).map (F.powIsoAlgebra M).obj.str :=
  rfl

/-- The iterated Weil structure, on the underlying sheaves, in terms of the algebra
`AlgebraicGeometry.WeilSheaf.powIsoAlgebra`. -/
lemma frobeniusPowStr_eq_powIsoAlgebra (F : WeilSheaf k₀ l X) (M : ℕ) :
    F.frobeniusPowStr M = (ProEtale.upperStarIsoLowerStarInv _ _).hom.app
      (F.powIsoAlgebra M).carrier.X ≫
        (ProEtale.AdicSheaf.forget _).map (F.powIsoAlgebra M).obj.str :=
  hom_app_comp_forget_map_frobeniusPowIso F M _

-- Stated for an arbitrary isomorphism `α`, for the same reason as
-- `hom_app_comp_forget_map_frobeniusPowIso` (about 75s for the concrete isomorphism).
private lemma hom_app_comp_inv_app_curvePullback (F : WeilSheaf k₀ l X)
    (α : ((Y ↘ Spec
        (CommRingCat.of L)).geometricGaloisFrobenius.asIso.hom)^*[WeilCoefficients.{u} l] ≅
      ((Y ↘ Spec
        (CommRingCat.of L)).geometricGaloisFrobenius.asIso.inv)_*[WeilCoefficients.{u} l]) :
    α.hom.app ((curvePullback j hj).obj F).obj.carrier.X ≫
      α.inv.app ((j)^*ᵃ[l].obj (F.powIsoAlgebra N).carrier).X = 𝟙 _ :=
  Iso.hom_inv_id_app _ _

private lemma upperStarIsoLowerStarInv_hom_inv_id_app_curvePullback (F : WeilSheaf k₀ l X) :
    (ProEtale.upperStarIsoLowerStarInv (WeilCoefficients.{u} l)
      (Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius.asIso).hom.app
        ((curvePullback j hj).obj F).obj.carrier.X ≫
    (ProEtale.upperStarIsoLowerStarInv (WeilCoefficients.{u} l)
      (Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius.asIso).inv.app
        ((j)^*ᵃ[l].obj (F.powIsoAlgebra N).carrier).X = 𝟙 _ :=
  hom_app_comp_inv_app_curvePullback j hj F _

/-- The Weil structure of the curve pullback, on the underlying sheaves: the pullback along `j`
of the iterated Weil structure `φ_N`, through
`Fr_Y^* j^* ≅ (Fr_Y ≫ j)^* = (j ≫ Fr^N)^* ≅ j^* (Fr^N)^*`. -/
lemma frobeniusStr_curvePullback (F : WeilSheaf k₀ l X) :
    ((curvePullback j hj).obj F).frobeniusStr =
      (ProEtale.upperStarComp _ (Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius.asIso.hom
          j).inv.app (F.powIsoAlgebra N).carrier.X ≫
        (ProEtale.upperStarCongr _ hj.symm).hom.app (F.powIsoAlgebra N).carrier.X ≫
        (ProEtale.upperStarComp _ j
          ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).asIso.hom).hom.app
          (F.powIsoAlgebra N).carrier.X ≫
        (j)^*[WeilCoefficients.{u} l].map
          ((ProEtale.upperStarIsoLowerStarInv _ _).hom.app (F.powIsoAlgebra N).carrier.X ≫
            (ProEtale.AdicSheaf.forget _).map (F.powIsoAlgebra N).obj.str) := by
  rw [frobeniusStr, IsoAlgebra.str_hom, curvePullback_obj_obj_obj_str, Functor.map_comp,
    Mod.forget_map, Mod.forget_map, adicUpperStar_map_hom,
    adicUpperStarCompFrobeniusIsoOfComm_hom_app_hom, Functor.map_comp,
    Mod.forget_map, Category.assoc]
  rw [← Category.assoc, upperStarIsoLowerStarInv_hom_inv_id_app_curvePullback, Category.id_comp]
  simp only [Category.assoc]

/-- The identity `j^* F̄ ⟶ j^* F̄` of the underlying sheaves of the curve pullback is compatible
with the Weil structure of the pullback and the iterated Weil structure `φ_N` of `F`. -/
lemma curvePullback_frobeniusStr_compatible (F : WeilSheaf k₀ l X) :
    (ProEtale.upperStarComp _ (Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius.asIso.hom
        j).hom.app (F.powIsoAlgebra N).carrier.X ≫
      ((Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius.asIso.hom)^*[_].map
        (𝟙 _ : (j)^*[WeilCoefficients.{u} l].obj (F.powIsoAlgebra N).carrier.X ⟶
          ((curvePullback j hj).obj F).obj.carrier.X) ≫
      ((curvePullback j hj).obj F).frobeniusStr =
    (ProEtale.upperStarCongr _ hj.symm).hom.app (F.powIsoAlgebra N).carrier.X ≫
      (ProEtale.upperStarComp _ j
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).asIso.hom).hom.app
          (F.powIsoAlgebra N).carrier.X ≫
      (j)^*[_].map (F.frobeniusPowStr N) ≫
      (𝟙 _ : (j)^*[WeilCoefficients.{u} l].obj (F.powIsoAlgebra N).carrier.X ⟶
          ((curvePullback j hj).obj F).obj.carrier.X) := by
  rw [frobeniusStr_curvePullback, frobeniusPowStr_eq_powIsoAlgebra, CategoryTheory.Functor.map_id]
  erw [Category.id_comp, Category.comp_id]
  rw [Iso.hom_inv_id_app_assoc]


/-- `j` intertwines the powers `Fr_Yᵐ` and `Fr^{N m}` of the geometric Galois Frobenii. -/
lemma comp_geometricGaloisFrobenius_pow_mul_eq
    (hj' : j ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).asIso.hom =
      (Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius.asIso.hom ≫ j) (m : ℕ) :
    j ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (N * m)).asIso.hom =
      ((Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius ^ m).asIso.hom ≫ j := by
  induction m with
  | zero =>
    rw [Nat.mul_zero, pow_zero, pow_zero]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  | succ m ih =>
    rw [Nat.mul_succ, ← Aut.pow_hom_comp_pow_hom, reassoc_of% hj', ih,
      ← Aut.pow_hom_comp_pow_hom _ m 1, pow_one, Category.assoc]

/-- The comparison of stalks `Γ(t^* F̄) ⟶ Γ(t'^* j^* F̄)` along a square `Θ ≫ t = t' ≫ j`
intertwines the transports along the iterated Weil structure `φ_N` of `F` and along the Weil
structure of its curve pullback. -/
lemma globalSectionsTransport_frobeniusPowStr_comp_curvePullback_one (F : WeilSheaf k₀ l X)
    {Θ : Spec (.of (AlgebraicClosure L)) ⟶ Spec (.of (AlgebraicClosure k₀))}
    {t₁ t₂ : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {t₁' t₂' : Spec (.of (AlgebraicClosure L)) ⟶ (Y ↘ Spec (CommRingCat.of L)).geometricFiber}
    {τ : Spec (.of (AlgebraicClosure k₀)) ⟶ Spec (.of (AlgebraicClosure k₀))}
    {τ' : Spec (.of (AlgebraicClosure L)) ⟶ Spec (.of (AlgebraicClosure L))}
    (h₁ : Θ ≫ t₁ = t₁' ≫ j) (h₂ : Θ ≫ t₂ = t₂' ≫ j)
    (hX : τ ≫ t₁ = t₂ ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).asIso.hom)
    (hY : τ' ≫ t₁' = t₂' ≫ ((Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius ^ 1).asIso.hom)
    (hΘ : τ' ≫ Θ = Θ ≫ τ) :
    ProEtale.globalSectionsTransport _ hX (F.frobeniusPowStr N) ≫
        ProEtale.globalSectionsTransport _ h₂
          (𝟙 _ : (j)^*[WeilCoefficients.{u} l].obj (F.powIsoAlgebra N).carrier.X ⟶
            ((curvePullback j hj).obj F).obj.carrier.X) =
      ProEtale.globalSectionsTransport _ h₁
          (𝟙 _ : (j)^*[WeilCoefficients.{u} l].obj (F.powIsoAlgebra N).carrier.X ⟶
            ((curvePullback j hj).obj F).obj.carrier.X) ≫
        ProEtale.globalSectionsTransport _ hY (((curvePullback j hj).obj F).frobeniusPowStr 1) := by
  have pY := congrArg (fun e ↦ e.asIso.hom)
    (pow_one (Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius)
  rw [ProEtale.globalSectionsTransport_congr _ hY pY _ _ (frobeniusPowStr_one _ pY)]
  exact ProEtale.globalSectionsTransport_comm_of_upperStar_of_comp _ j _ _
    hj.symm _ _ _ (curvePullback_frobeniusStr_compatible j hj F) h₁ h₂ hX _ hΘ

/-- The comparison of stalks `Γ(t^* F̄) ⟶ Γ(t'^* j^* F̄)` along a square `Θ ≫ t = t' ≫ j`
intertwines the transports along the iterated Weil structures `φ_{N m}` of `F` and `φ_m` of its
curve pullback, `m ≥ 1`. -/
lemma globalSectionsTransport_frobeniusPowStr_comp_curvePullback (hN : 1 ≤ N)
    (F : WeilSheaf k₀ l X) (m : ℕ) (hm : 1 ≤ m)
    {Θ : Spec (.of (AlgebraicClosure L)) ⟶ Spec (.of (AlgebraicClosure k₀))}
    {t₁ t₂ : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {t₁' t₂' : Spec (.of (AlgebraicClosure L)) ⟶ (Y ↘ Spec (CommRingCat.of L)).geometricFiber}
    {τ : Spec (.of (AlgebraicClosure k₀)) ⟶ Spec (.of (AlgebraicClosure k₀))}
    {τ' : Spec (.of (AlgebraicClosure L)) ⟶ Spec (.of (AlgebraicClosure L))}
    (h₁ : Θ ≫ t₁ = t₁' ≫ j) (h₂ : Θ ≫ t₂ = t₂' ≫ j)
    (hX : τ ≫ t₁ =
      t₂ ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (N * m)).asIso.hom)
    (hY : τ' ≫ t₁' = t₂' ≫ ((Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius ^ m).asIso.hom)
    (hΘ : τ' ≫ Θ = Θ ≫ τ) :
    ProEtale.globalSectionsTransport _ hX (F.frobeniusPowStr (N * m)) ≫
        ProEtale.globalSectionsTransport _ h₂
          (𝟙 _ : (j)^*[WeilCoefficients.{u} l].obj (F.powIsoAlgebra N).carrier.X ⟶
            ((curvePullback j hj).obj F).obj.carrier.X) =
      ProEtale.globalSectionsTransport _ h₁
          (𝟙 _ : (j)^*[WeilCoefficients.{u} l].obj (F.powIsoAlgebra N).carrier.X ⟶
            ((curvePullback j hj).obj F).obj.carrier.X) ≫
        ProEtale.globalSectionsTransport _ hY (((curvePullback j hj).obj F).frobeniusPowStr m) := by
  induction m, hm using Nat.le_induction generalizing t₁ t₂ t₁' t₂' τ τ' with
  | base =>
    have hX' : τ ≫ t₁ =
        t₂ ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).asIso.hom := by
      rw [hX, Nat.mul_one]
    rw [globalSectionsTransport_frobeniusPowStr_congr F (Nat.mul_one N) rfl hX hX']
    exact globalSectionsTransport_frobeniusPowStr_comp_curvePullback_one j hj F h₁ h₂ hX' hY hΘ
  | succ m hm ih =>
    have pc' : j ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (N * m)).asIso.inv =
        ((Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius ^ m).asIso.inv ≫ j := by
      rw [← cancel_mono
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (N * m)).asIso.hom,
        Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
        comp_geometricGaloisFrobenius_pow_mul_eq j hj m, Iso.inv_hom_id_assoc]
    have haX : (Iso.refl _).hom ≫ t₁ =
        (t₁ ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (N * m)).asIso.inv) ≫
          ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (N * m)).asIso.hom := by
      simp
    have hbX : τ ≫
        (t₁ ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (N * m)).asIso.inv) =
        t₂ ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).asIso.hom := by
      rw [← cancel_mono
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (N * m)).asIso.hom,
        Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, hX, Category.assoc,
        Aut.pow_hom_comp_pow_hom, Nat.mul_succ]
    have haY : (Iso.refl _).hom ≫ t₁' =
        (t₁' ≫ ((Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius ^ m).asIso.inv) ≫
          ((Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius ^ m).asIso.hom := by
      simp
    have hbY : τ' ≫ (t₁' ≫ ((Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius ^ m).asIso.inv) =
        t₂' ≫ ((Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius ^ 1).asIso.hom := by
      rw [← cancel_mono ((Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius ^ m).asIso.hom,
        Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, hY, Category.assoc,
        Aut.pow_hom_comp_pow_hom]
    have hmid : Θ ≫
        (t₁ ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (N * m)).asIso.inv) =
        (t₁' ≫ ((Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius ^ m).asIso.inv) ≫ j := by
      rw [← Category.assoc, h₁, Category.assoc, pc', Category.assoc]
    have hΘ₀ : (Iso.refl _).hom ≫ Θ = Θ ≫ (Iso.refl _).hom := by simp
    have hX'' : τ ≫ t₁ =
        t₂ ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (N * m + N)).asIso.hom := by
      rw [hX, Nat.mul_succ]
    rw [globalSectionsTransport_frobeniusPowStr_congr F (Nat.mul_succ N m) rfl hX hX'',
      ← F.globalSectionsTransport_frobeniusPowStr_comp (N * m) N hN haX hbX (Category.comp_id τ)
        hX'',
      ← ((curvePullback j hj).obj F).globalSectionsTransport_frobeniusPowStr_comp m 1 le_rfl haY
        hbY (Category.comp_id τ') hY, Category.assoc,
      globalSectionsTransport_frobeniusPowStr_comp_curvePullback_one j hj F hmid h₂ hbX hbY hΘ,
      ← Category.assoc, ih h₁ hmid haX haY hΘ₀, Category.assoc]

/-- The underlying sheaf of the curve pullback is the pullback of the underlying sheaf. -/
noncomputable def curvePullbackCompForgetIso :
    curvePullback (l := l) j hj ⋙ (WeilSheaf.objectProperty L l Y).ι ⋙ IsoAlgebra.forget _ ≅
      (WeilSheaf.objectProperty k₀ l X).ι ⋙ IsoAlgebra.forget _ ⋙ (j)^*ᵃ[l] :=
  NatIso.ofComponents (fun F ↦ eqToIso (curvePullback_obj_obj_carrier j hj F)) fun _ ↦
    (Category.comp_id _).trans (Category.id_comp _).symm

-- Deduced from `curvePullbackCompForgetIso` rather than proved on morphisms: the kernel compares
-- the sums of morphisms of the two algebras `F` and `F.powIsoAlgebra N` with the same underlying
-- sheaf slowly (about 30s).
instance : (curvePullback (l := l) j hj).Additive := by
  have : @Functor.Additive (WeilSheaf k₀ l X) _ _ _ _ _ (WeilSheaf.objectProperty k₀ l X).ι :=
    Functor.fullSubcategoryInclusion_additive _
  have : @Functor.Additive (WeilSheaf L l Y) _ _ _ _ _ (WeilSheaf.objectProperty L l Y).ι :=
    Functor.fullSubcategoryInclusion_additive _
  have : ((curvePullback (l := l) j hj ⋙ (WeilSheaf.objectProperty L l Y).ι) ⋙
      IsoAlgebra.forget _).Additive :=
    Functor.additive_of_iso (Functor.associator _ _ _ ≪≫ curvePullbackCompForgetIso j hj).symm
  have : (curvePullback (l := l) j hj ⋙ (WeilSheaf.objectProperty L l Y).ι).Additive :=
    Functor.additive_of_comp_faithful _ (IsoAlgebra.forget _)
  exact Functor.additive_of_comp_faithful _ (WeilSheaf.objectProperty L l Y).ι

instance [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    PreservesFiniteLimits (curvePullback (l := l) j hj) := by
  have : PreservesFiniteLimits ((curvePullback (l := l) j hj ⋙
      (WeilSheaf.objectProperty L l Y).ι) ⋙ IsoAlgebra.forget _) :=
    preservesFiniteLimits_of_natIso
      (Functor.associator _ _ _ ≪≫ curvePullbackCompForgetIso j hj).symm
  have : PreservesFiniteLimits (curvePullback (l := l) j hj ⋙
      (WeilSheaf.objectProperty L l Y).ι) :=
    preservesFiniteLimits_of_reflects_of_preserves _ (IsoAlgebra.forget _)
  have : ReflectsFiniteLimits (WeilSheaf.objectProperty L l Y).ι :=
    ReflectsLimitsOfSize.reflectsFiniteLimits.{0, 0} _
  exact preservesFiniteLimits_of_reflects_of_preserves _ (WeilSheaf.objectProperty L l Y).ι

instance [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    PreservesFiniteColimits (curvePullback (l := l) j hj) := by
  have : PreservesFiniteColimits ((curvePullback (l := l) j hj ⋙
      (WeilSheaf.objectProperty L l Y).ι) ⋙ IsoAlgebra.forget _) :=
    preservesFiniteColimits_of_natIso
      (Functor.associator _ _ _ ≪≫ curvePullbackCompForgetIso j hj).symm
  have : PreservesFiniteColimits (curvePullback (l := l) j hj ⋙
      (WeilSheaf.objectProperty L l Y).ι) :=
    preservesFiniteColimits_of_reflects_of_preserves _ (IsoAlgebra.forget _)
  have : ReflectsFiniteColimits (WeilSheaf.objectProperty L l Y).ι :=
    ReflectsColimitsOfSize.reflectsFiniteColimits.{0, 0} _
  exact preservesFiniteColimits_of_reflects_of_preserves _ (WeilSheaf.objectProperty L l Y).ι

/-- The pullback of a lisse Weil sheaf is lisse. -/
theorem IsLisse.curvePullback {F : WeilSheaf k₀ l X} (hF : F.IsLisse) :
    ((WeilSheaf.curvePullback j hj).obj F).IsLisse :=
  IsAdicLisseSheaf.upperStar j hF

/-- The pullback along `j` of a lisse subsheaf `P ⊆ F̄` fixed by the `N`-th iterate of the
Frobenius twist: a lisse Weil sheaf on `Y` over `L`, with underlying sheaf `j^* P`. -/
noncomputable def curvePullbackSub (F : WeilSheaf k₀ l X) (P : Subobject F.obj.carrier)
    (hP : (⇑F.frobeniusTwist)^[N] P = P) (hPl : IsAdicLisseSheaf (Subobject.underlying.obj P)) :
    WeilSheaf L l Y :=
  ⟨(ProEtaleWeilSheaf.equivariantPullback _ j hj).obj (F.stableIsoAlgebra P hP),
    hPl.isAdicConstructibleSheaf.upperStar j⟩

/-- The inclusion `j^* P ⟶ j^* F̄` of the pullback of a subsheaf defined over `L`. -/
noncomputable def curvePullbackSubι (F : WeilSheaf k₀ l X) (P : Subobject F.obj.carrier)
    (hP : (⇑F.frobeniusTwist)^[N] P = P) (hPl : IsAdicLisseSheaf (Subobject.underlying.obj P)) :
    curvePullbackSub j hj F P hP hPl ⟶ (curvePullback j hj).obj F :=
  ObjectProperty.homMk ((ProEtaleWeilSheaf.equivariantPullback _ j hj).map
    (F.stableIsoAlgebraι P hP))

@[simp]
lemma curvePullbackSub_obj_carrier (F : WeilSheaf k₀ l X) (P : Subobject F.obj.carrier)
    (hP : (⇑F.frobeniusTwist)^[N] P = P) (hPl : IsAdicLisseSheaf (Subobject.underlying.obj P)) :
    (curvePullbackSub j hj F P hP hPl).obj.carrier = (j)^*ᵃ[l].obj (Subobject.underlying.obj P) :=
  rfl

lemma curvePullbackSubι_hom_hom_f (F : WeilSheaf k₀ l X) (P : Subobject F.obj.carrier)
    (hP : (⇑F.frobeniusTwist)^[N] P = P) (hPl : IsAdicLisseSheaf (Subobject.underlying.obj P)) :
    (curvePullbackSubι j hj F P hP hPl).hom.hom.f = (j)^*ᵃ[l].map P.arrow :=
  rfl

instance (F : WeilSheaf k₀ l X) (P : Subobject F.obj.carrier)
    (hP : (⇑F.frobeniusTwist)^[N] P = P) (hPl : IsAdicLisseSheaf (Subobject.underlying.obj P)) :
    Mono (curvePullbackSubι j hj F P hP hPl) := by
  have : Mono (curvePullbackSubι j hj F P hP hPl).hom.hom.f := by
    rw [curvePullbackSubι_hom_hom_f]
    infer_instance
  have : Mono (curvePullbackSubι j hj F P hP hPl).hom.hom :=
    (Algebra.forget _).mono_of_mono_map this
  have : Mono (curvePullbackSubι j hj F P hP hPl).hom :=
    (IsoAlgebra.ι _).mono_of_mono_map this
  exact (WeilSheaf.objectProperty L l Y).ι.mono_of_mono_map this

/-- The pullback of a subsheaf defined over `L` is lisse. -/
theorem isLisse_curvePullbackSub (F : WeilSheaf k₀ l X) (P : Subobject F.obj.carrier)
    (hP : (⇑F.frobeniusTwist)^[N] P = P) (hPl : IsAdicLisseSheaf (Subobject.underlying.obj P)) :
    (curvePullbackSub j hj F P hP hPl).IsLisse :=
  IsAdicLisseSheaf.upperStar j hPl

/-- If the pullback `j^* P` is an irreducible local system, then the Weil sheaf
`curvePullbackSub j hj F P` is irreducible lisse. -/
theorem isIrreducibleLisse_curvePullbackSub [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of L))]
    (F : WeilSheaf k₀ l X) (P : Subobject F.obj.carrier)
    (hP : (⇑F.frobeniusTwist)^[N] P = P) (hPl : IsAdicLisseSheaf (Subobject.underlying.obj P))
    (hirr : IsIrreducibleAdicLocalSystem ((j)^*ᵃ[l].obj (Subobject.underlying.obj P))) :
    (curvePullbackSub j hj F P hP hPl).IsIrreducibleLisse := by
  refine ⟨isLisse_curvePullbackSub j hj F P hP hPl,
    fun h ↦ hirr.2.1 (isZero_iff_isZero_carrier.mp h), fun H i hi hH ↦ ?_⟩
  have : Mono (((WeilSheaf.objectProperty L l Y).ι ⋙ IsoAlgebra.forget _).map i) :=
    Functor.map_mono _ i
  have : Mono i.hom.hom.f := this
  have hm : Mono (i.hom.hom.f ≫ eqToHom (curvePullbackSub_obj_carrier j hj F P hP hPl)) :=
    mono_comp _ _
  rcases hirr.2.2 _ _ hm hH with h | h
  · exact Or.inl (isZero_iff_isZero_carrier.mpr h)
  · have : IsIso i.hom.hom.f := IsIso.of_isIso_comp_right _
      (eqToHom (curvePullbackSub_obj_carrier j hj F P hP hPl))
    have : IsIso ((Algebra.forget _).map i.hom.hom) := this
    have : IsIso i.hom.hom := isIso_of_reflects_iso _ (Algebra.forget _)
    have : IsIso ((IsoAlgebra.ι _).map i.hom) := this
    have : IsIso i.hom := isIso_of_reflects_iso _ (IsoAlgebra.ι _)
    have : IsIso ((WeilSheaf.objectProperty L l Y).ι.map i) := this
    exact Or.inr (isIso_of_fully_faithful (WeilSheaf.objectProperty L l Y).ι i)

end WeilSheaf

end AlgebraicGeometry
