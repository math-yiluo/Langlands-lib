/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegersSheafStratumIdentification
public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeIdentification
public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeScalarLinear

/-!
# `Rⁱg_* ℚ̄_ℓ,T` is lisse on a connected stratum

Let `g : T ⟶ Y` be quasi-compact and quasi-separated, `E` a finite extension of `ℚ_ℓ` with
`ℤ_ℓ → 𝒪_E` surjective (i.e. `E = ℚ_ℓ`) and `j = i ≫ o : S ⟶ Y` a stratum over which the torsion
direct images `Rᵏg_* (𝒪_E ⧸ ℓ)_T` are finite locally constant, with `S` connected (given with
universal covers). Then `j^* Rⁱg_* ℚ̄_ℓ,T` is lisse
(`isAdicLisseSheaf_upperStar_adicRightDerivedLowerStarUnit_of_universalCovers`), provided the maps
`ψ_U : C(U, M) → (p^* j^* Rⁱg_* ℚ̄_ℓ,T)(U)` induced by isomorphisms
`θ : C(-, M) ≅ (p ≫ j)^* Rⁱg_* 𝒪_{E,T}` are `C(U, 𝒪_E)`-semilinear
(`AlgebraicGeometry.ProEtale.IntegralLatticeSemilinear`), which is kept as a hypothesis. The
inputs are:

- the sheaf-level integral identification `θ : C(-, M) ≅ (p ≫ j)^* Rⁱg_* 𝒪_{E,T}` on a universal
  cover `p` of `S` (`nonempty_iso_upperStar_rightDerived_integersStratum`), with `M = lim_n Gₙ` a
  finite `𝒪_E`-module with its `ℓ`-adic topology
  (`AlgebraicGeometry.ProEtale.towerLimit_finite_integersStratum`,
  `AlgebraicGeometry.ProEtale.towerLimit_isModuleTopology_integersStratum`);
- its `𝒪_E`-linearity (`AlgebraicGeometry.ProEtale.integralLattice_map_smul_of_surjective`);
- the lisse criterion for identifications along `p ≫ j`
  (`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.of_integralLatticeIdentification`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite PadicAlgCl TopologicalSpace

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (l : ℕ) [Fact l.Prime]

/-- `ℚ_ℓ`, as a finite subextension of `ℚ̄_ℓ`. -/
noncomputable abbrev finiteIntermediateFieldBot : FiniteIntermediateField l :=
  ⟨⊥, inferInstance⟩

/-- The `ℓ`-adic topology on the ring of integers `𝒪_E` of a finite extension `E ⊆ ℚ̄_ℓ` of
`ℚ_ℓ`, restricted from `ℚ̄_ℓ`. -/
noncomputable abbrev integersTopology (E : FiniteIntermediateField l) :
    TopologicalSpace (integers l E.1) :=
  letI := normedFieldOfAlgebra l E.1
  inferInstance

/-- **Semilinearity of integral identifications**: for every weakly étale `p : S ⟶ S₀`, every
`j : S₀ ⟶ Y`, every finite `𝒪_E`-module `M` and every isomorphism
`θ : C(-, M) ≅ (p ≫ j)^* Rⁱg_* 𝒪_{E,T}` of abelian sheaves, `𝒪_E` carrying its `ℓ`-adic topology,
the induced maps `ψ_U : C(U, M) → (p^* j^* Rⁱg_* ℚ̄_ℓ,T)(U)` are `C(U, 𝒪_E)`-semilinear. -/
def IntegralLatticeSemilinear {T Y : Scheme.{u}} (g : T ⟶ Y) (i : ℕ)
    (E : FiniteIntermediateField l) : Prop :=
  ∀ ⦃S S₀ : Scheme.{u}⦄ (p : S ⟶ S₀) [WeaklyEtale p] (j : S₀ ⟶ Y) (M : Type) [AddCommGroup M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [TopologicalSpace (integers l E.1)]
    [IsTopologicalRing (integers l E.1)] [Module (integers l E.1) M]
    [Module.Finite (integers l E.1) M] [ContinuousSMul (integers l E.1) M]
    (hι : Continuous (algebraMap (integers l E.1) (PadicAlgCl l)))
    (_ : ‹TopologicalSpace (integers l E.1)› = integersTopology l E)
    (θ : continuousMapAddSheaf S M ⟶ (p ≫ j)^*[Ab.{u + 1}].obj
      (((g)_*[Ab.{u + 1}].rightDerived i).obj
        ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (padicIntegersSheaf T l E.1))))
    [IsIso θ] (U : S.ProEt) (f : C(U.left, integers l E.1)) (m : C(U.left, M)),
    integralLatticeSectionsOfIdentification
        ((AdicAbIdentification.ofUpperStar g i j).upperStar p) E θ U (f • m) =
      AdicSheaf.sectionAct _
        (ULift.up (AdicSheaf.ringValuedFunction _ hι (algebraMap_integers_mem l E.1) f))
        (integralLatticeSectionsOfIdentification
          ((AdicAbIdentification.ofUpperStar g i j).upperStar p) E θ U m)

section Finite

variable (E : Type) [Field E] [Algebra E (PadicAlgCl l)] [Algebra ℚ_[l] E]
  [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]

/-- **The limit of the stalks over a stratum is a finite `𝒪_E`-module**, under the hypotheses of
`AlgebraicGeometry.ProEtale.towerLimit_isModuleTopology_integersStratum`. -/
theorem towerLimit_finite_integersStratum {T Y S : Scheme.{u}} (g : T ⟶ Y) (j : S ⟶ Y)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S) (k : ℕ)
    (h : Etale.flcProperty S (upperStarRightDerivedIntegersModL l E g j k))
    (hH' : ∀ n : ℕ, IsSetFLC ((Etale.upperStar (ModuleCat.{u + 1} (integersShrink.{u} l E))
      j).obj ((Etale.higherDirectImageQuotPowTower (integersShrinkIdeal.{u} l E) g
        k).obj (op n)))) :
    let G := Etale.higherDirectImageQuotPowTower (integersShrinkIdeal.{u} l E) g k ⋙
      Etale.upperStar (ModuleCat.{u + 1} (integersShrink.{u} l E)) j ⋙
        (pointSmallEtale s).sheafFiber
    have (n : ℕ) : Small.{0} (G.obj (op n)) :=
      have : Finite (G.obj (op n)) := (hH' n).finite_sheafFiber s
      inferInstance
    letI := ModuleCat.towerLimitModuleOf G (shrinkRingEquiv.{0, u} l E)
    Module.Finite (integers l E) (ModuleCat.towerLimit G) := by
  intro G _
  have := Etale.finite_limit_sheafFiber_upperStar_higherDirectImageQuotPowTower
    (integersShrinkIdeal.{u} l E) g (natCast_mem_nonZeroDivisors_shrink l E) rfl j s k h
  exact ModuleCat.towerLimit_finite_of_ringEquiv G (shrinkRingEquiv.{0, u} l E)

end Finite

variable (E : FiniteIntermediateField l)

/-- **`j^* Rⁱg_* ℚ̄_ℓ,T` is lisse on a connected stratum** `j = i ≫ o` (`i` a closed immersion into
a scheme with noetherian underlying space, `o` an open immersion) with universal covers, over
which all the `Rᵏg_* (ℤ_ℓ ⧸ ℓ)_T` are finite locally constant, provided the integral
identifications are semilinear. -/
theorem isAdicLisseSheaf_upperStar_adicRightDerivedLowerStarUnit_of_universalCovers
    {T Y S U : Scheme.{u}} (g : T ⟶ Y) [QuasiCompact g] [QuasiSeparated g] [NoetherianSpace U]
    (i : S ⟶ U) [IsClosedImmersion i] (o : U ⟶ Y) [IsOpenImmersion o]
    (h : ∀ k : ℕ, Etale.flcProperty S
      (upperStarRightDerivedIntegersModL l E.1 g (i ≫ o) k))
    {Ω : Type u} [Field Ω] (Ũ : Scheme.UniversalCovers S Ω)
    (y : Spec (.of (AlgebraicClosure Ω)) ⟶ S) (k : ℕ)
    (hsurj : Function.Surjective (integersPadicIntHom l E.1))
    (hψι : IntegralLatticeSemilinear l g k E) :
    IsAdicLisseSheaf ((i ≫ o)^*ᵃ[l].obj (adicRightDerivedLowerStarUnit l g k)) := by
  have := Ũ.weaklyEtale_proj y
  have : Surjective (Ũ.proj y) := ⟨Ũ.surjective_proj y⟩
  have := Ũ.quasiCompact_proj y
  obtain ⟨θ⟩ := nonempty_iso_upperStar_rightDerived_integersStratum l E.1 g i o h Ũ y k
  have hH' (n : ℕ) := isSetFLC_upperStar_higherDirectImageQuotPowTower_integers l E.1 g
    (i ≫ o) h n (k : ℤ)
  let G := Etale.higherDirectImageQuotPowTower (integersShrinkIdeal.{u} l E.1) g k ⋙
    Etale.upperStar (ModuleCat.{u + 1} (integersShrink.{u} l E.1)) (i ≫ o) ⋙
      (pointSmallEtale (Ũ.pt y ≫ Ũ.proj y)).sheafFiber
  have (n : ℕ) : Small.{0} (G.obj (op n)) :=
    have : Finite (G.obj (op n)) := (hH' n).finite_sheafFiber _
    inferInstance
  let := ModuleCat.towerLimitModuleOf G (shrinkRingEquiv.{0, u} l E.1)
  have := towerLimit_finite_integersStratum l E.1 g (i ≫ o) (Ũ.pt y ≫ Ũ.proj y) k (h k) hH'
  let θ' : continuousMapAddSheaf (Ũ.cover y) (ModuleCat.towerLimit G) ⟶
      (Ũ.proj y ≫ i ≫ o)^*[Ab.{u + 1}].obj (((g)_*[Ab.{u + 1}].rightDerived k).obj
        ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
          (padicIntegersSheaf T l E.1))) := θ.hom
  have : IsIso θ' := inferInstanceAs (IsIso θ.hom)
  let : TopologicalSpace (integers l E.1) := integersTopology l E
  have : IsTopologicalRing (integers l E.1) := isTopologicalRing_integers l E.1
  have : CompactSpace (integers l E.1) := compactSpace_integers l E.1
  have : IsModuleTopology (integers l E.1) (ModuleCat.towerLimit G) :=
    towerLimit_isModuleTopology_integersStratum l E.1 g (i ≫ o) (Ũ.pt y ≫ Ũ.proj y) k (h k) hH'
  have hι : Continuous (algebraMap (integers l E.1) (PadicAlgCl l)) :=
    continuous_algebraMap_integers l E.1
  have hκ : Continuous (integersPadicIntHom l E.1) := continuous_integersPadicIntHom l E.1
  have iCS : ContinuousSMul (integers l E.1) (ModuleCat.towerLimit G) :=
    IsModuleTopology.toContinuousSMul _ _
  have hθ (U : (Ũ.cover y).ProEt) [IsAffine U.left] (r : integers l E.1)
      (m : C(U.left, ModuleCat.towerLimit G)) :=
    integralLattice_map_smul_of_surjective g (Ũ.proj y ≫ i ≫ o) k E θ' hsurj U r m
  have hψι' := hψι (Ũ.proj y) (i ≫ o) (ModuleCat.towerLimit G) hι rfl θ'
  exact IsAdicLisseSheaf.of_integralLatticeIdentification E (Ũ.proj y)
    ((AdicAbIdentification.ofUpperStar g k (i ≫ o)).upperStar (Ũ.proj y)) θ' hι hκ
    (algebraMap_integersPadicIntHom l E.1) (fun U _ r m ↦ hθ U r m) hψι'

end AlgebraicGeometry.ProEtale
