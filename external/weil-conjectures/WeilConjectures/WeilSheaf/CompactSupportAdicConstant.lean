/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.Constant
public import WeilConjectures.WeilSheaf.LowerStar
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
import WeilConjectures.WeilSheaf.CohomologyProEtale
import WeilConjectures.WeilSheaf.LowerShriek
import WeilConjectures.WeilSheaf.CohomologyNonneg
import WeilConjectures.AlgebraicGeometry.DenseCompactification
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
import WeilConjectures.WeilSheaf.OpenClosedTriangle
import WeilConjectures.WeilSheaf.CohomologyAdicConstant
import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantCohomologicalDimension

/-!
# Compactly supported cohomology of the constant Weil sheaf

Let `X` be a separated `k₀`-scheme of finite type whose geometric fiber `X ⊗ k̄` has dimension
at most `e`. Then `H_c^r(X ⊗ k̄, ℚ̄_ℓ) = 0` for `r ∉ [0, 2e]`. Choose a dense compactification
`j : X ⟶ X'` with `dim X' = dim X` and let `i : W ⟶ X'` be its closed complement, of dimension
`< e`. The open–closed triangle gives the exact sequence
`H^{r-1}(W, i^*ℚ̄_ℓ) ⟶ H_c^r(X, j^*ℚ̄_ℓ) ⟶ H^r(X', ℚ̄_ℓ)`, whose outer terms vanish for `r > 2e`
(`AlgebraicGeometry.WeilSheaf.subsingleton_cohomology_adicConstant_of_two_mul_lt`); and the
vanishing of `H_c^r` only depends on the underlying `ℓ`-adic sheaf, which is `ℚ̄_ℓ` for `j^*ℚ̄_ℓ`.

## Main statements

- `AlgebraicGeometry.ProEtaleWeilSheaf.nonempty_lowerStarCohomologyIso`: for a pro-étale Weil
  sheaf `G` on `Y` and `φ : Y ⟶ Spec k₀`, the global sections of the `r`-th cohomology sheaf of
  `Rφ_* G` are the pro-étale cohomology `Rʳ Γ(Ȳ_proét, G)` of the underlying sheaf.
- `AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_of_iso`: the vanishing
  of `H_c^r(X ⊗ k̄, F)` only depends on the underlying `ℓ`-adic sheaf of `F`.
- `AlgebraicGeometry.topologicalKrullDim_compl_add_one_le_of_dense`: the complement of a dense
  open subset has smaller dimension.
- `WeilSheaf.subsingleton_compactlySupportedCohomology_adicConstant_of_two_mul_lt`:
  the vanishing of `H_c^r(X ⊗ k̄, ℚ̄_ℓ)` for `r ∉ [0, 2e]`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

open scoped AlgebraicGeometry.ProEtale

-- `Spec k₀` over itself: prefer the identity structure over `AlgebraicGeometry.specOverSpec`,
-- which is imported through the étale cohomological dimension bound.
attribute [local instance 1100] CategoryTheory.instOverClass

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace ProEtaleWeilSheaf

variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
  (φ : Y ⟶ Spec (CommRingCat.of k₀)) [φ.IsOver (Spec (CommRingCat.of k₀))]

omit [Fact (ringChar k₀ ≠ l)] in
/-- **Cohomology of the direct image to `Spec k₀` is pro-étale cohomology.** For a pro-étale Weil
sheaf `G` on `Y` and `φ : Y ⟶ Spec k₀`, the global sections over `Spec k̄` of the `r`-th
cohomology sheaf of `Rφ_* G` are the pro-étale cohomology `Rʳ Γ(Ȳ_proét, G)` of the underlying
sheaf of `ℚ̄_ℓ`-modules: forgetting the Weil structure and the module structure commutes with
`Rφ̄_*`, `Γ(Spec k̄, -)` is exact and `Γ(Spec k̄, φ̄_* -) = Γ(Ȳ, -)`. -/
theorem nonempty_lowerStarCohomologyIso (G : ProEtaleWeilSheaf k₀ l Y) (r : ℕ) :
    Nonempty (
    (IsoAlgebra.forget _ ⋙ ProEtale.AdicSheaf.forget _ ⋙ Sheaf.Γ _ (WeilCoefficients.{u} l)).obj
        ((_root_.DerivedCategory.homologyFunctor _ (r : ℤ)).obj
          ((ProEtaleWeilSheaf.lowerStar k₀ l φ).rightDerivedFunctor.obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj G))) ≅
      ((Sheaf.Γ (Scheme.ProEt.topology (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber)
        (WeilCoefficients.{u} l)).rightDerived r).obj ((ProEtale.AdicSheaf.forget _).obj
          G.carrier)) := by
  set φ' := Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀)))
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  -- forget the Weil structure: `For (Rφ_* G) ≅ Rφ̄_* (For G)`
  let e₁ : (IsoAlgebra.forget _).mapDerivedCategory.obj
      ((ProEtaleWeilSheaf.lowerStar k₀ l φ).rightDerivedFunctor.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj G)) ≅
      (φ')_*ᵃ[l].rightDerivedFunctor.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj G.carrier) :=
    (IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso _ _).app _ ≪≫
      Functor.mapIso _ (((IsoAlgebra.forget _).mapDerivedCategorySingleFunctor 0).app G)
  -- forget the `ℚ̄_ℓ,Ȳ`-module structure
  let e₂ : (ProEtale.AdicSheaf.forget _).mapDerivedCategory.obj
      ((φ')_*ᵃ[l].rightDerivedFunctor.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj G.carrier)) ≅
      ((φ')_*[WeilCoefficients.{u} l]).rightDerivedFunctor.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((ProEtale.AdicSheaf.forget _).obj G.carrier)) :=
    ((ProEtale.mapDerivedCategoryForgetCompRightDerivedLowerStarIso l φ').app _).symm ≪≫
      Functor.mapIso _
        (((ProEtale.AdicSheaf.forget _).mapDerivedCategorySingleFunctor 0).app G.carrier)
  -- the underlying sheaf of `𝓗ʳ(Rφ_* G)` is `Rʳφ̄_* G`
  let e₃ : (ProEtale.AdicSheaf.forget _).obj ((IsoAlgebra.forget _).obj
      ((_root_.DerivedCategory.homologyFunctor _ (r : ℤ)).obj
        ((ProEtaleWeilSheaf.lowerStar k₀ l φ).rightDerivedFunctor.obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj G)))) ≅
      (((φ')_*[WeilCoefficients.{u} l]).rightDerived r).obj
        ((ProEtale.AdicSheaf.forget _).obj G.carrier) :=
    (ProEtale.AdicSheaf.forget _).mapIso
        ((((IsoAlgebra.forget _).mapDerivedCategoryHomologyFunctorIso (r : ℤ)).app _) ≪≫
          (_root_.DerivedCategory.homologyFunctor _ (r : ℤ)).mapIso e₁) ≪≫
      (((ProEtale.AdicSheaf.forget _).mapDerivedCategoryHomologyFunctorIso (r : ℤ)).app _) ≪≫
      (_root_.DerivedCategory.homologyFunctor _ (r : ℤ)).mapIso e₂ ≪≫
      ((φ')_*[WeilCoefficients.{u} l]).homologyRightDerivedFunctorObjSingleFunctorIso _ r
  -- `Γ(Spec k̄, -)` is exact and `Γ(Spec k̄, φ̄_* -) = Γ(Ȳ, -)`
  exact ⟨(Sheaf.Γ _ (WeilCoefficients.{u} l)).mapIso e₃ ≪≫
    (Functor.rightDerivedCompObjIso _ _ r _).symm ≪≫
    Functor.rightDerivedObjIsoOfIso (ProEtale.globalSectionsLowerStarIso _ φ') r _⟩

end ProEtaleWeilSheaf

section Dimension

open Order Topology TopologicalSpace

/-- In a noetherian quasi-sober `T₀` space, the complement of a dense open subset `U` has
strictly smaller dimension: every point `x ∉ U` is a proper specialization of the generic point
of an irreducible component, which lies in `U`. -/
theorem topologicalKrullDim_compl_add_one_le_of_dense {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] [QuasiSober X] [T0Space X] {U : Set X} (hU : IsOpen U)
    (hd : Dense U) : topologicalKrullDim (Uᶜ : Set X) + 1 ≤ topologicalKrullDim X := by
  have : QuasiSober (Uᶜ : Set X) := hU.isClosed_compl.isClosedEmbedding_subtypeVal.quasiSober
  let oC := specializationOrder (Uᶜ : Set X)
  rcases isEmpty_or_nonempty (Uᶜ : Set X) with hE | hE
  · rw [topologicalKrullDim_eq_krullDim_specializationOrder (X := (Uᶜ : Set X)),
      krullDim_eq_bot]
    simp
  have : Nonempty X := ⟨hE.some.1⟩
  rw [topologicalKrullDim_eq_krullDim_specializationOrder (X := (Uᶜ : Set X)),
    krullDim_eq_iSup_height_of_nonempty, ← WithBot.coe_one, ← WithBot.coe_add, ENat.iSup_add]
  let oX := specializationOrder X
  rw [topologicalKrullDim_eq_krullDim_specializationOrder (X := X),
    @krullDim_eq_iSup_height_of_nonempty X oX.toPreorder _]
  have hmono : @StrictMono (Uᶜ : Set X) X oC.toPreorder oX.toPreorder Subtype.val := by
    intro a b hab
    have hle : b ⤳ a := hab.le
    refine @lt_of_le_of_ne X oX _ _ ?_ fun h ↦ (@ne_of_lt _ oC.toPreorder _ _ hab) (Subtype.ext h)
    exact (IsInducing.subtypeVal.specializes_iff (x := b) (y := a)).2 hle
  refine WithBot.coe_le_coe.2 (iSup_le fun a ↦ ?_)
  obtain ⟨η, -, hη, hηa⟩ := isClosed_univ.exists_maximal_specializes (Set.mem_univ a.1)
  have hηU : η ∈ U :=
    mem_of_dense_of_forall_specializes_eq hU hd fun y hy ↦ hη y trivial hy
  have hlt : @LT.lt X oX.toLT a.1 η :=
    @lt_of_le_of_ne X oX _ _ hηa fun h ↦ a.2 (by rw [h]; exact hηU)
  calc @height _ oC.toPreorder a + 1 ≤ @height X oX.toPreorder a.1 + 1 := by
        gcongr
        exact @height_le_height_apply_of_strictMono _ X oC.toPreorder oX.toPreorder _ hmono a
    _ ≤ @height X oX.toPreorder η := @height_add_one_le X oX.toPreorder _ _ hlt
    _ ≤ ⨆ x, @height X oX.toPreorder x := le_iSup (fun x : X ↦ @height X oX.toPreorder x) η

end Dimension

namespace WeilSheaf

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

attribute [local instance] Compactification.over in
/-- **The vanishing of compactly supported cohomology only depends on the underlying sheaf.** If
the underlying `ℓ`-adic sheaves of two Weil sheaves `F` and `G` on `X` are isomorphic, then
`H_c^r(X ⊗ k̄, G) = 0` implies `H_c^r(X ⊗ k̄, F) = 0`: for the chosen compactification
`X ⟶[i] Z ⟶[g] Spec k₀`, `H_c^r(X ⊗ k̄, F)` is the pro-étale cohomology
`Rʳ Γ(Z̄_proét, ī_! F)`, which only depends on the underlying sheaf of `F`. -/
theorem subsingleton_compactlySupportedCohomology_of_iso {F G : WeilSheaf k₀ l X}
    (e : F.obj.carrier ≅ G.obj.carrier) (r : ℤ)
    (hG : Subsingleton (G.compactlySupportedCohomology r).carrier) :
    Subsingleton (F.compactlySupportedCohomology r).carrier := by
  obtain hr | hr := lt_or_ge r 0
  · exact subsingleton_compactlySupportedCohomology_of_neg F hr
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, r = n := ⟨r.toNat, by lia⟩
  let c := HasCompactification.compactification (X ↘ Spec (CommRingCat.of k₀))
    (hf := hasCompactification_of_over (k₀ := k₀) _)
  let Φ : ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ⥤
      WeilCoefficients.{u} l :=
    ProEtale.adicOpenImmersionLowerShriek l
        (Scheme.Hom.geometricFiberMap c.i (comp_over c.i (Spec (CommRingCat.of k₀)))) ⋙
      ProEtale.AdicSheaf.forget _ ⋙
        (Sheaf.Γ (Scheme.ProEt.topology (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiber)
          (WeilCoefficients.{u} l)).rightDerived n
  have key (H : WeilSheaf k₀ l X) : Nonempty
      ((IsoAlgebra.forget _ ⋙ ProEtale.AdicSheaf.forget _ ⋙
        Sheaf.Γ _ (WeilCoefficients.{u} l)).obj
          ((_root_.DerivedCategory.homologyFunctor _ (n : ℤ)).obj
            ((ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.obj
              ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).mapDerivedCategory.obj
                ((_root_.DerivedCategory.singleFunctor _ 0).obj H.obj)))) ≅
        Φ.obj H.obj.carrier) := by
    obtain ⟨e₁⟩ := ProEtaleWeilSheaf.nonempty_lowerStarCohomologyIso c.g
      ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).obj H.obj) n
    exact ⟨(IsoAlgebra.forget _ ⋙ ProEtale.AdicSheaf.forget _ ⋙
        Sheaf.Γ _ (WeilCoefficients.{u} l)).mapIso
          ((_root_.DerivedCategory.homologyFunctor _ (n : ℤ)).mapIso
            ((ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.mapIso
              (((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).mapDerivedCategorySingleFunctor
                0).app H.obj))) ≪≫ e₁ ≪≫
      ((Sheaf.Γ _ (WeilCoefficients.{u} l)).rightDerived n).mapIso
        ((ProEtale.AdicSheaf.forget _).mapIso
          ((IsoAlgebra.mapOfNatIsoCompForgetIso
            (ProEtale.adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso l c.i
              (comp_over c.i _))).app H.obj))⟩
  obtain ⟨eF⟩ := key F
  obtain ⟨eG⟩ := key G
  have hz : IsZero ((IsoAlgebra.forget _ ⋙ ProEtale.AdicSheaf.forget _ ⋙
      Sheaf.Γ _ (WeilCoefficients.{u} l)).obj
        ((_root_.DerivedCategory.homologyFunctor _ (n : ℤ)).obj
          ((ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.obj
            ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).mapDerivedCategory.obj
              ((_root_.DerivedCategory.singleFunctor _ 0).obj G.obj))))) :=
    @ModuleCat.isZero_of_subsingleton _ _ _ hG
  exact ModuleCat.subsingleton_of_isZero ((WeilCoefficients.toModuleCat l).map_isZero
    (hz.of_iso (eF ≪≫ Φ.mapIso e ≪≫ eG.symm)))

end WeilSheaf

namespace WeilSheaf

/-- A Weil sheaf whose underlying `ℓ`-adic sheaf is the constant sheaf `ℚ̄_ℓ` has no cohomology
above twice the dimension of the geometric fiber. -/
theorem subsingleton_cohomology_of_carrier_iso_unit {Y : Scheme.{u}}
    [Y.Over (Spec (CommRingCat.of k₀))] [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l Y)
    (eF : F.obj.carrier ≅ ProEtale.AdicSheaf.unit l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (d : ℕ)
    (hd : topologicalKrullDim (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber ≤ (d : WithBot ℕ∞))
    (r : ℕ) (hr : 2 * d < r) : Subsingleton (F.cohomology r).carrier :=
  subsingleton_cohomology_of_isZero_rightDerived F r
    ((ProEtale.isZero_rightDerived_Γ_adicConstantSheaf_of_two_mul_lt
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure d hd r hr).of_iso
        (((Sheaf.Γ _ (WeilCoefficients.{u} l)).rightDerived r).mapIso
          ((ProEtale.AdicSheaf.forget _).mapIso eF)))

omit [Finite k₀] [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] in
/-- The geometric fiber of a `k₀`-scheme locally of finite type has the same dimension as the
scheme. -/
lemma topologicalKrullDim_geometricFiber (Y : Scheme.{u}) [Y.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] :
    topologicalKrullDim (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber = topologicalKrullDim Y :=
  topologicalKrullDim_pullback_eq_of_field _ (Scheme.specAlgebraicClosure k₀).hom

variable (k₀ l) in
/-- **Compactly supported cohomology of `ℚ̄_ℓ` in high degrees.** If the geometric fiber
`X ⊗ k̄` of a separated `k₀`-scheme of finite type has dimension at most `e`, then
`H_c^r(X ⊗ k̄, ℚ̄_ℓ) = 0` for `r < 0` and for `r > 2e`.

Choose a dense compactification `X ⟶[j] X' ⟶ Spec k₀` with `dim X' = dim X`
(`AlgebraicGeometry.exists_dense_compactification`) and let `W = X' ∖ X`, with
`dim W < dim X'`. The open–closed triangle gives the exact sequence
`H^{r-1}(W, ℚ̄_ℓ) ⟶ H_c^r(X, j^*ℚ̄_ℓ) ⟶ H^r(X', ℚ̄_ℓ)` of compactly supported cohomology, both
outer terms vanishing for `r > 2e`, and `j^*ℚ̄_ℓ` has the same underlying sheaf as `ℚ̄_ℓ`. -/
theorem subsingleton_compactlySupportedCohomology_adicConstant_of_two_mul_lt (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))] [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] (e : ℕ)
    (he : topologicalKrullDim (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ≤ (e : WithBot ℕ∞))
    (r : ℤ) (hr : r < 0 ∨ 2 * (e : ℤ) < r) :
    Subsingleton ((adicConstant k₀ l X).compactlySupportedCohomology r).carrier := by
  obtain hr | hr := hr
  · exact subsingleton_compactlySupportedCohomology_of_neg _ hr
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, r = n + 1 := ⟨(r - 1).toNat, by lia⟩
  have hX : topologicalKrullDim X ≤ e := (topologicalKrullDim_geometricFiber X).symm.trans_le he
  obtain ⟨X', aX', j, hprop, hj, hcomm, hdense, hdim⟩ :=
    exists_dense_compactification (X ↘ Spec (CommRingCat.of k₀))
  let : X'.Over (Spec (CommRingCat.of k₀)) := ⟨aX'⟩
  have : IsProper (X' ↘ Spec (CommRingCat.of k₀)) := hprop
  have : IsOpenImmersion j := hj
  have : j.IsOver (Spec (CommRingCat.of k₀)) := ⟨hcomm⟩
  have hX' : topologicalKrullDim (X' ↘ Spec (CommRingCat.of k₀)).geometricFiber ≤ e := by
    rw [topologicalKrullDim_geometricFiber, hdim]
    exact hX
  -- the closed complement `W` of `X` in `X'`
  let C : TopologicalSpace.Closeds X' :=
    ⟨(Set.range j.base)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩
  let W := (Scheme.IdealSheafData.vanishingIdeal C).subscheme
  let i : W ⟶ X' := (Scheme.IdealSheafData.vanishingIdeal C).subschemeι
  have : IsClosedImmersion i :=
    inferInstanceAs (IsClosedImmersion (Scheme.IdealSheafData.vanishingIdeal C).subschemeι)
  have hrange : Set.range i.base = (Set.range j.base)ᶜ :=
    (Scheme.IdealSheafData.range_subschemeι _).trans
      (by simp [Scheme.IdealSheafData.coe_support_vanishingIdeal, C])
  let : W.Over (Spec (CommRingCat.of k₀)) := ⟨i ≫ aX'⟩
  have : i.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : IsProper (W ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (IsProper (i ≫ aX'))
  by_cases hW : IsEmpty W
  · -- `X = X'` is proper, and `H_c = H`
    have hsurj : Function.Surjective j.base := fun x ↦ by
      by_contra hx
      obtain ⟨w, -⟩ : x ∈ Set.range i.base := by
        rw [hrange]
        exact fun ⟨y, hy⟩ ↦ hx ⟨y, hy⟩
      exact hW.false w
    have : Epi j.base := (TopCat.epi_iff_surjective _).2 hsurj
    have : IsIso j := IsOpenImmersion.isIso j
    have : IsProper (X ↘ Spec (CommRingCat.of k₀)) := by
      rw [← comp_over j (Spec (CommRingCat.of k₀))]
      infer_instance
    have := subsingleton_cohomology_adicConstant_of_two_mul_lt k₀ l X e he
      (r := (n : ℤ) + 1) (Or.inr hr)
    exact @Equiv.subsingleton _ _ (WeilComplex.cohomologyEquivOfIso
      (WeilComplex.derivedLowerShriekObjIsoDerivedLowerStar (X ↘ Spec (CommRingCat.of k₀))
        (toComplex.obj (adicConstant k₀ l X))) ((n : ℤ) + 1)).toLinearEquiv.toEquiv this
  rw [not_isEmpty_iff] at hW
  -- `dim W < dim X' ≤ e`
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian aX'
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace aX'
  have : IsNoetherian X' := ⟨⟩
  have hWdim : topologicalKrullDim W + 1 ≤ e := by
    rw [i.isClosedEmbedding.isEmbedding.topologicalKrullDim_eq_range, hrange]
    exact (topologicalKrullDim_compl_add_one_le_of_dense j.isOpenEmbedding.isOpen_range
      hdense).trans (hdim.trans_le hX)
  have hne : topologicalKrullDim W ≠ ⊥ := by
    rw [topologicalKrullDim, Ne, Order.krullDim_eq_bot_iff, not_isEmpty_iff]
    exact ⟨⟨closure {hW.some}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.1 hne
  rw [← hm] at hWdim
  have hm' : m + 1 ≤ (e : ℕ∞) := by exact_mod_cast hWdim
  have hmtop : m ≠ ⊤ := by
    rintro rfl
    simp at hm'
  obtain ⟨d, rfl⟩ := ENat.ne_top_iff_exists.1 hmtop
  have hde : d + 1 ≤ e := by exact_mod_cast hm'
  have hW' : topologicalKrullDim (W ↘ Spec (CommRingCat.of k₀)).geometricFiber ≤ d := by
    rw [topologicalKrullDim_geometricFiber, ← hm]
    exact_mod_cast le_rfl
  -- the open–closed triangle `Ra_{X!} j^*ℚ̄_ℓ ⟶ Ra_{X'!} ℚ̄_ℓ ⟶ Ra_{W!} i^*ℚ̄_ℓ ⟶`
  obtain ⟨α, β, γ, hT⟩ := WeilComplex.exists_distTriang_derivedLowerShriek_structure_openClosed
    j i hrange (toComplex.obj (adicConstant k₀ l X'))
  set T := Pretriangulated.Triangle.mk α β γ
  have h₂ : Subsingleton (T.obj₂.cohomologyFrobeniusModule ((n : ℤ) + 1)).carrier := by
    have := subsingleton_cohomology_adicConstant_of_two_mul_lt k₀ l X' e hX'
      (r := (n : ℤ) + 1) (Or.inr hr)
    exact @Equiv.subsingleton _ _ (WeilComplex.cohomologyEquivOfIso
      (WeilComplex.derivedLowerShriekObjIsoDerivedLowerStar (X' ↘ Spec (CommRingCat.of k₀))
        (toComplex.obj (adicConstant k₀ l X'))) ((n : ℤ) + 1)).toLinearEquiv.toEquiv this
  have h₃ : Subsingleton (T.obj₃.cohomologyFrobeniusModule n).carrier := by
    have := subsingleton_cohomology_of_carrier_iso_unit
      ((WeilSheaf.upperStar i).obj (adicConstant k₀ l X'))
      (ProEtale.adicUpperStarUnitIso l _) d hW' n (by lia)
    exact @Equiv.subsingleton _ _ (WeilComplex.cohomologyEquivOfIso
      (WeilComplex.derivedLowerShriekObjIsoDerivedLowerStar (W ↘ Spec (CommRingCat.of k₀)) _ ≪≫
        (WeilComplex.derivedLowerStar (W ↘ Spec (CommRingCat.of k₀))).mapIso
          ((toComplexCompUpperStarIso i).app (adicConstant k₀ l X'))) n).toLinearEquiv.toEquiv this
  have h₁ : Subsingleton (T.obj₁.cohomologyFrobeniusModule ((n : ℤ) + 1)).carrier := by
    refine ⟨fun x y ↦ ?_⟩
    have hex := WeilComplex.exact_cohomologyδ_right T n ((n : ℤ) + 1) rfl hT
    have hx (x : (T.obj₁.cohomologyFrobeniusModule ((n : ℤ) + 1)).carrier) : x = 0 := by
      obtain ⟨z, rfl⟩ := (hex x).1 (Subsingleton.elim _ _)
      rw [Subsingleton.elim z 0, map_zero]
    rw [hx x, hx y]
  have hG : Subsingleton (((WeilSheaf.upperStar j).obj
      (adicConstant k₀ l X')).compactlySupportedCohomology ((n : ℤ) + 1)).carrier :=
    let eT := WeilComplex.cohomologyEquivOfIso
      ((WeilComplex.derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).mapIso
        ((toComplexCompUpperStarIso j).app (adicConstant k₀ l X'))) ((n : ℤ) + 1)
    @Equiv.subsingleton _ _ eT.symm.toLinearEquiv.toEquiv h₁
  exact subsingleton_compactlySupportedCohomology_of_iso (ProEtale.adicUpperStarUnitIso l _).symm
    _ hG

end WeilSheaf

end AlgebraicGeometry
