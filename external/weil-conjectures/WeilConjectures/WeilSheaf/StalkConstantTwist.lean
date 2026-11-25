/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.ConstantTwistCohomology
public import WeilConjectures.WeilSheaf.StalkCharpoly

/-!
# Stalks of constant Weil twists

The constant Weil twist `F ⊗ 𝓑_b` of a Weil sheaf `F` by a unit `b ∈ ℚ̄_ℓˣ`
(`AlgebraicGeometry.WeilSheaf.constantTwist`) has the underlying sheaf of `F` and the Weil
structure `b • φ`. Its iterated Weil structure is `bᵐ • φ_m`, so the Frobenius of its stalks
relative to `𝔽_{qᵐ}` is `bᵐ` times that of `F`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalk_constantTwist`: at a closed point of degree
  `m`, the stalk of `F ⊗ 𝓑_b` is the stalk of `F` with its local Frobenius multiplied by `bᵐ`
  (blueprint: `proposition-twisting-weight-zero-adding-dual--2`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

open scoped AlgebraicGeometry.ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The Weil structure of `F ⊗ 𝓑_b` is `b • φ`. -/
lemma constantTwist_obj_str_hom (F : WeilSheaf k₀ l X) (b : (PadicAlgCl l)ˣ) :
    (F.constantTwist b).obj.str.hom =
      F.obj.str.hom ≫ ProEtale.AdicSheaf.smul (ULift.up (b : PadicAlgCl l)) F.obj.carrier :=
  rfl

/-- The iterated Weil structure of a constant twist `F ⊗ 𝓑_b` is `bᵐ • φ_m`. -/
lemma frobeniusPowIso_constantTwist_hom (F : WeilSheaf k₀ l X) (b : (PadicAlgCl l)ˣ) (m : ℕ) :
    ((F.constantTwist b).frobeniusPowIso m).hom =
      (F.frobeniusPowIso m).hom ≫ ProEtale.AdicSheaf.smul (ULift.up ((b ^ m : (PadicAlgCl l)ˣ) :
        PadicAlgCl l)) F.obj.carrier := by
  induction m with
  | zero =>
    have h₁ : ProEtale.AdicSheaf.smul (ULift.up ((b ^ 0 : (PadicAlgCl l)ˣ) : PadicAlgCl l))
        F.obj.carrier = 𝟙 _ := by
      rw [pow_zero, Units.val_one]
      exact ProEtale.AdicSheaf.smul_one _
    rw [h₁, Category.comp_id]
    rfl
  | succ m ih =>
    simp only [frobeniusPowIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom]
    rw [ih, Functor.map_comp, ProEtale.AdicSheaf.adicLowerStar_map_smul,
      constantTwist_obj_str_hom]
    simp only [Category.assoc]
    rw [reassoc_of% ProEtale.AdicSheaf.smul_comp, ProEtale.AdicSheaf.smul_smul]
    have hb : (ULift.up (b : PadicAlgCl l) * ULift.up ((b ^ m : (PadicAlgCl l)ˣ) : PadicAlgCl l) :
        ULift.{u + 1} (PadicAlgCl l)) =
          ULift.up ((b ^ (m + 1) : (PadicAlgCl l)ˣ) : PadicAlgCl l) := by
      rw [pow_succ', Units.val_mul]
      rfl
    rw [hb]
    rfl

-- Stated for a variable isomorphism `α`: for the concrete `upperStarIsoLowerStarInv` the kernel
-- times out comparing the two objects, which agree only up to unfolding `constantTwist`.
private lemma app_constantTwist_carrier (F : WeilSheaf k₀ l X) (b : (PadicAlgCl l)ˣ)
    {P Q : Sheaf (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (WeilCoefficients.{u} l) ⥤
        Sheaf (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
          (WeilCoefficients.{u} l)} (α : P ≅ Q) :
    α.hom.app (F.constantTwist b).obj.carrier.X = α.hom.app F.obj.carrier.X :=
  rfl

/-- The iterated Weil structure of `F ⊗ 𝓑_b`, on the underlying sheaves, is `bᵐ • φ_m`. -/
lemma frobeniusPowStr_constantTwist (F : WeilSheaf k₀ l X) (b : (PadicAlgCl l)ˣ) (m : ℕ) :
    (F.constantTwist b).frobeniusPowStr m = F.frobeniusPowStr m ≫
      ((ULift.up ((b ^ m : (PadicAlgCl l)ˣ) : PadicAlgCl l)) • 𝟙 F.obj.carrier.X) := by
  rw [frobeniusPowStr, frobeniusPowIso_constantTwist_hom, Functor.map_comp, frobeniusPowStr,
    Category.assoc]
  exact congrArg (· ≫ _) (app_constantTwist_carrier F b _)

omit [Finite k₀] [Fact (ringChar k₀ ≠ l)] in
/-- Transports of global sections are `ℚ̄_ℓ`-linear in the structure map. -/
lemma globalSectionsTransport_comp_smul {P P' Y' : Scheme.{u}} {τ : P' ⟶ P}
    {t : P ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber} {t' : P' ⟶ Y'}
    {g : Y' ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber} (h : τ ≫ t = t' ≫ g)
    {M : Sheaf (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (WeilCoefficients.{u} l)} {N : ProEtale.AdicSheaf l Y'}
    (ψ : (g)^*[WeilCoefficients.{u} l].obj M ⟶ N.X) (c : ULift.{u + 1} (PadicAlgCl l)) :
    ProEtale.globalSectionsTransport _ h (ψ ≫ (c • 𝟙 N.X)) =
      ProEtale.globalSectionsTransport _ h ψ ≫ (c • 𝟙 _) := by
  have : (Sheaf.Γ (Scheme.ProEt.topology P') (WeilCoefficients.{u} l)).Linear
      (ULift.{u + 1} (PadicAlgCl l)) :=
    (constantSheafΓAdj _ _).right_adjoint_linear
  have ht : (t')^*[WeilCoefficients.{u} l].map (c • 𝟙 N.X) = c • 𝟙 _ := by
    have := congrArg Mod.Hom.hom (ProEtale.AdicSheaf.adicUpperStar_map_smul t' c N)
    rw [ProEtale.adicUpperStar_map_hom, ProEtale.AdicSheaf.smul_hom,
      ProEtale.AdicSheaf.smul_hom] at this
    exact this
  simp only [ProEtale.globalSectionsTransport, Functor.map_comp, ht, Functor.map_smul,
    CategoryTheory.Functor.map_id, Category.assoc]

omit [Finite k₀] [Fact (ringChar k₀ ≠ l)] in
private lemma toModuleCat_map_smul_comp {M N : WeilCoefficients.{u} l} (f : M ⟶ N)
    (c : ULift.{u + 1} (PadicAlgCl l)) :
    ((WeilCoefficients.toModuleCat l).map (f ≫ (c • 𝟙 N))).hom =
      c.down • ((WeilCoefficients.toModuleCat l).map f).hom := by
  ext x
  rfl

/-- The Frobenius of the stalk of `F ⊗ 𝓑_b` relative to `𝔽_{qᵐ}` is `bᵐ` times that of `F`. -/
lemma frobeniusEnd_stalkAt_constantTwist (F : WeilSheaf k₀ l X) (b : (PadicAlgCl l)ˣ)
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (m : ℕ) (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s) :
    ((F.constantTwist b).stalkAt s m hs).frobeniusEnd =
      (b : PadicAlgCl l) ^ m • (F.stalkAt s m hs).frobeniusEnd := by
  rw [frobeniusEnd_stalkAt, frobeniusEnd_stalkAt, frobeniusPowStr_constantTwist,
    globalSectionsTransport_comp_smul (N := F.obj.carrier), ← Units.val_pow_eq_pow_val]
  exact toModuleCat_map_smul_comp _ _

/-- The stalk of `F ⊗ 𝓑_b` at a geometric point, with its Frobenius relative to `𝔽_{qᵐ}`, is the
stalk of `F` with its Frobenius multiplied by `bᵐ`. -/
lemma nonempty_equiv_stalkAt_constantTwist (F : WeilSheaf k₀ l X) (b : (PadicAlgCl l)ˣ)
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (m : ℕ) (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s) :
    Nonempty (((F.constantTwist b).stalkAt s m hs).Equiv
      ((F.stalkAt s m hs).rescale ((b : PadicAlgCl l) ^ m))) :=
  ⟨.ofComp (LinearEquiv.refl _ _) (by
    rw [LinearEquiv.refl_toLinearMap, LinearMap.id_comp, LinearMap.comp_id,
      frobeniusEnd_stalkAt_constantTwist]
    exact LinearMap.ext fun v ↦ (FrobeniusModule.frobeniusEnd_rescale_apply
      (M := F.stalkAt s m hs) (pow_ne_zero _ b.ne_zero) v).symm)⟩

/-- At a closed point `x` of degree `m`, the stalk of the constant twist `F ⊗ 𝓑_b` is the stalk
of `F` with its local Frobenius multiplied by `bᵐ`. (blueprint:
`proposition-twisting-weight-zero-adding-dual--2`) -/
theorem nonempty_equiv_stalk_constantTwist (F : WeilSheaf k₀ l X) (b : (PadicAlgCl l)ˣ)
    (x : X.finitePoints) :
    Nonempty (((F.constantTwist b).stalk x).Equiv ((F.stalk x).rescale
      ((b : PadicAlgCl l) ^ (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1))) :=
  nonempty_equiv_stalkAt_constantTwist F b _ _ _

end AlgebraicGeometry.WeilSheaf
