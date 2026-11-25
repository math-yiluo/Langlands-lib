/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.FrobeniusTwistSubobject
public import WeilConjectures.WeilSheaf.StalkComparison
public import WeilConjectures.DeligneLaumon.Reduction.RealCurveConstituent

/-!
# Frobenius-module isomorphisms of twisted stalks

Let `F` be a Weil sheaf on a `k₀`-scheme `X` and `t` a geometric point of `X̄` with
`t ≫ Frᴺ = σᴺ ≫ t`. The identifications `F_{t ≫ Frᵃ} ≅ F_t` (induced by the iterated Weil
structure) and `F_{σᵃ ≫ t} ≅ F_t` (reparametrisation) are isomorphisms of Frobenius modules for
the Frobenius relative to `𝔽_{q^N}`
(`AlgebraicGeometry.WeilSheaf.stalkAtFrobeniusPowEquiv`,
`AlgebraicGeometry.WeilSheaf.stalkAtSpecFrobeniusPowEquiv`). The first carries the stalk of a
subsheaf `P` onto the stalk of its `a`-th Frobenius twist, the second the stalk of `P` onto the
stalk of `P`.

As a consequence, purity of the stalk of `P` at a Frobenius translate of `t` gives purity of the
stalk of `Tᵃ P` at `t`
(`AlgebraicGeometry.WeilSheaf.isPureOfWeightOn_stalkSubspace_frobeniusTwist_iterate`).

The isomorphisms are built from transports along squares
(`AlgebraicGeometry.ProEtale.globalSectionsTransport`), with the compatibility with the
Frobenius stated at the level of linear maps, which keeps the kernel checks fast.
-/

@[expose] public section

universe u

open CategoryTheory Limits

-- As in `WeilConjectures.WeilSheaf.CurvePullback`: elaborating through these instances produces
-- terms which the kernel compares slowly with the imported ones.
attribute [-instance] ModuleCat.instIsRightAdjointForgetLinearMapIdCarrier
  ModuleCat.isGrothendieckAbelian_of_commRing
  CategoryTheory.hasGlobalSectionsFunctor_of_hasLimitsOfShape

namespace FrobeniusModule

variable {K : Type*} [Field K]

@[simp]
lemma Equiv.ofComp_toLinearEquiv {M N : FrobeniusModule.{u} K} (e : M.carrier ≃ₗ[K] N.carrier)
    (h : e.toLinearMap ∘ₗ M.frobeniusEnd = N.frobeniusEnd ∘ₗ e.toLinearMap) :
    (Equiv.ofComp e h).toLinearEquiv = e :=
  rfl

end FrobeniusModule

namespace AlgebraicGeometry.WeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {ι : PadicAlgCl l →+* ℂ} {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  (F : WeilSheaf k₀ l X)

/-- A transport of stalks `F_s ⟶ F_{s'}` along a square `g ≫ s = s' ≫ Frʲ`, with `g` commuting
with `σᵐ`, intertwines the Frobenius relative to `𝔽_{qᵐ}` (for all `j` and `m`). -/
lemma toModuleCat_map_globalSectionsTransport_comp_frobeniusEnd_stalkAt'
    {s s' : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {g : Spec (.of (AlgebraicClosure k₀)) ⟶ Spec (.of (AlgebraicClosure k₀))} {j m : ℕ}
    (hg : g ≫ s = s' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ j).asIso.hom)
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s)
    (hs' : s' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s')
    (hcomm : g ≫ (specGeometricFrobenius k₀ ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ g) :
    ((WeilCoefficients.toModuleCat l).map
        (ProEtale.globalSectionsTransport _ hg (F.frobeniusPowStr j))).hom ∘ₗ
        (F.stalkAt s m hs).frobeniusEnd =
      (F.stalkAt s' m hs').frobeniusEnd ∘ₗ ((WeilCoefficients.toModuleCat l).map
        (ProEtale.globalSectionsTransport _ hg (F.frobeniusPowStr j))).hom := by
  rw [frobeniusEnd_stalkAt, frobeniusEnd_stalkAt, ← WeilCoefficients.toModuleCat_map_comp_hom,
    ← WeilCoefficients.toModuleCat_map_comp_hom,
    F.globalSectionsTransport_frobeniusPowStr_comm' j m hg hs.symm hs'.symm hcomm]

/-- The isomorphism `F_{t ≫ Frᵃ} ≅ F_t` of the iterated Weil structure, as an isomorphism of
Frobenius modules for the Frobenius relative to `𝔽_{q^N}`. -/
noncomputable def stalkAtFrobeniusPowEquiv
    {t : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {N : ℕ} (ht : t ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).asIso.hom =
      (specGeometricFrobenius k₀ ^ N).asIso.hom ≫ t) (a : ℕ)
    (ht' : (t ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ a).asIso.hom) ≫
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).asIso.hom =
        (specGeometricFrobenius k₀ ^ N).asIso.hom ≫
          t ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ a).asIso.hom) :
    (F.stalkAt _ N ht').Equiv (F.stalkAt t N ht) :=
  have hg : (Iso.refl (Spec (.of (AlgebraicClosure k₀)))).hom ≫
      t ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ a).asIso.hom =
        t ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ a).asIso.hom :=
    Category.id_comp _
  have := F.isIso_globalSectionsTransport_frobeniusPowStr a hg
  .ofComp (WeilCoefficients.linearEquivOfIso
      (asIso (ProEtale.globalSectionsTransport _ hg (F.frobeniusPowStr a))))
    (by
      rw [WeilCoefficients.linearEquivOfIso_toLinearMap, asIso_hom]
      exact F.toModuleCat_map_globalSectionsTransport_comp_frobeniusEnd_stalkAt' hg ht' ht
        (by simp))

/-- The isomorphism `F_{t ≫ Frᵃ} ≅ F_t` of Frobenius modules carries the stalk of `P` at
`t ≫ Frᵃ` onto the stalk of the `a`-th Frobenius twist of `P` at `t`. -/
theorem map_stalkAtFrobeniusPowEquiv_stalkSubspace
    {t : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {N : ℕ} (ht : t ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).asIso.hom =
      (specGeometricFrobenius k₀ ^ N).asIso.hom ≫ t) (a : ℕ)
    (ht' : (t ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ a).asIso.hom) ≫
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).asIso.hom =
        (specGeometricFrobenius k₀ ^ N).asIso.hom ≫
          t ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ a).asIso.hom)
    (P : Subobject F.obj.carrier) :
    (F.stalkSubspace _ P).map (F.stalkAtFrobeniusPowEquiv ht a ht').toLinearEquiv.toLinearMap =
      F.stalkSubspace t ((⇑F.frobeniusTwist)^[a] P) := by
  rw [stalkSubspace_frobeniusTwist_iterate, stalkAtFrobeniusPowEquiv,
    FrobeniusModule.Equiv.ofComp_toLinearEquiv, WeilCoefficients.linearEquivOfIso_toLinearMap,
    WeilCoefficients.linearEquivOfIso_toLinearMap, asIso_hom,
    F.stalkObjFrobeniusPowIso_hom_eq_globalSectionsTransport a t (Category.id_comp _)]

/-- The reparametrisation `F_{σᵃ ≫ t} ≅ F_t`, as an isomorphism of Frobenius modules for the
Frobenius relative to `𝔽_{q^N}`. -/
noncomputable def stalkAtSpecFrobeniusPowEquiv
    {t : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {N : ℕ} (ht : t ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).asIso.hom =
      (specGeometricFrobenius k₀ ^ N).asIso.hom ≫ t) (a : ℕ)
    (ht' : ((specGeometricFrobenius k₀ ^ a).asIso.hom ≫ t) ≫
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).asIso.hom =
        (specGeometricFrobenius k₀ ^ N).asIso.hom ≫ (specGeometricFrobenius k₀ ^ a).asIso.hom ≫ t) :
    (F.stalkAt _ N ht').Equiv (F.stalkAt t N ht) :=
  have hg : (specGeometricFrobenius k₀ ^ a).asIso.hom ≫ t =
      ((specGeometricFrobenius k₀ ^ a).asIso.hom ≫ t) ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).asIso.hom := by
    rw [pow_zero]
    exact (Category.comp_id _).symm
  have := F.isIso_globalSectionsTransport_frobeniusPowStr 0 hg
  FrobeniusModule.Equiv.symm <| .ofComp (WeilCoefficients.linearEquivOfIso
      (asIso (ProEtale.globalSectionsTransport _ hg (F.frobeniusPowStr 0))))
    (by
      rw [WeilCoefficients.linearEquivOfIso_toLinearMap, asIso_hom]
      exact F.toModuleCat_map_globalSectionsTransport_comp_frobeniusEnd_stalkAt' hg ht ht'
        (by rw [Aut.pow_hom_comp_pow_hom, Aut.pow_hom_comp_pow_hom, Nat.add_comm]))

/-- The reparametrisation `F_{σᵃ ≫ t} ≅ F_t` of Frobenius modules carries the stalk of `P` at
`σᵃ ≫ t` onto the stalk of `P` at `t`. -/
theorem map_stalkAtSpecFrobeniusPowEquiv_stalkSubspace
    {t : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {N : ℕ} (ht : t ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).asIso.hom =
      (specGeometricFrobenius k₀ ^ N).asIso.hom ≫ t) (a : ℕ)
    (ht' : ((specGeometricFrobenius k₀ ^ a).asIso.hom ≫ t) ≫
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).asIso.hom =
        (specGeometricFrobenius k₀ ^ N).asIso.hom ≫ (specGeometricFrobenius k₀ ^ a).asIso.hom ≫ t)
    (P : Subobject F.obj.carrier) :
    (F.stalkSubspace _ P).map
        (F.stalkAtSpecFrobeniusPowEquiv ht a ht').toLinearEquiv.toLinearMap =
      F.stalkSubspace t P := by
  rw [stalkAtSpecFrobeniusPowEquiv, FrobeniusModule.Equiv.symm_toLinearEquiv,
    FrobeniusModule.Equiv.ofComp_toLinearEquiv, Submodule.map_symm_eq_iff,
    WeilCoefficients.linearEquivOfIso_toLinearMap, asIso_hom,
    ← F.stalkObjSpecFrobeniusPowIso_inv_eq_globalSectionsTransport a t, ← Iso.symm_hom,
    ← WeilCoefficients.linearEquivOfIso_toLinearMap, WeilCoefficients.linearEquivOfIso_symm,
    Submodule.map_symm_eq_iff]
  exact F.stalkSubspace_specGeometricFrobenius_pow t P a

/-- Purity on the stalk of a subsheaf only depends on the geometric point. -/
theorem isPureOfWeightOn_stalkSubspace_congr
    {t t' : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    (h : t = t') {m : ℕ}
    (ht : t ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ t)
    (ht' : t' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ t')
    (P : Subobject F.obj.carrier) (q : ℕ) (w : ℝ) :
    (F.stalkAt t m ht).IsPureOfWeightOn ι q (F.stalkSubspace t P) w ↔
      (F.stalkAt t' m ht').IsPureOfWeightOn ι q (F.stalkSubspace t' P) w := by
  subst h
  rfl

/-- **Purity on the Frobenius translates of a geometric point** (blueprint:
`theorem-real-constructible-sheaves-are-mixed--1`, "the weight obtained on this curve is independent
of the curve"). Let `s` be a geometric point with `σᵃ ≫ s = t ≫ Frᵃ`, e.g. the translate
`σ⁻ᵃ ≫ t ≫ Frᵃ` of `t`. If the stalk of `P` at `s` is pure of weight `w`, so is the stalk of the
`a`-th Frobenius twist `Tᵃ P` at `t`. -/
theorem isPureOfWeightOn_stalkSubspace_frobeniusTwist_iterate
    {t s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {m : ℕ} (ht : t ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ t) (a : ℕ)
    (hσs : (specGeometricFrobenius k₀ ^ a).asIso.hom ≫ s =
      t ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ a).asIso.hom)
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s)
    (P : Subobject F.obj.carrier) (q : ℕ) (w : ℝ)
    (h : (F.stalkAt s m hs).IsPureOfWeightOn ι q (F.stalkSubspace s P) w) :
    (F.stalkAt t m ht).IsPureOfWeightOn ι q
      (F.stalkSubspace t ((⇑F.frobeniusTwist)^[a] P)) w := by
  have h₂ : (t ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ a).asIso.hom) ≫
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
        (specGeometricFrobenius k₀ ^ m).asIso.hom ≫
          t ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ a).asIso.hom := by
    rw [Category.assoc, Aut.pow_hom_comp_pow_hom, add_comm, ← Aut.pow_hom_comp_pow_hom,
      reassoc_of% ht]
  have h₁ : ((specGeometricFrobenius k₀ ^ a).asIso.hom ≫ s) ≫
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
        (specGeometricFrobenius k₀ ^ m).asIso.hom ≫
          (specGeometricFrobenius k₀ ^ a).asIso.hom ≫ s := by
    rw [hσs]
    exact h₂
  -- from `s` to `σᵃ ≫ s`
  have h' : (F.stalkAt _ m h₁).IsPureOfWeightOn ι q (F.stalkSubspace _ P) w :=
    FrobeniusModule.IsPureOfWeightOn.of_map_eq _
      (F.stalkAtSpecFrobeniusPowEquiv hs a h₁).map_frobenius
      (F.map_stalkAtSpecFrobeniusPowEquiv_stalkSubspace hs a h₁ P) h
  -- from `σᵃ ≫ s = t ≫ Frᵃ` to `t`
  exact ((F.isPureOfWeightOn_stalkSubspace_congr hσs h₁ h₂ P q w).1 h').map_eq _
    (F.stalkAtFrobeniusPowEquiv ht a h₂).map_frobenius
    (F.map_stalkAtFrobeniusPowEquiv_stalkSubspace ht a h₂ P)

end AlgebraicGeometry.WeilSheaf
