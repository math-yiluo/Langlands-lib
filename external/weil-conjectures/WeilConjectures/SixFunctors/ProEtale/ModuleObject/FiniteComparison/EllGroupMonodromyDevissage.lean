/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.Biduality.EtaleReductionDualizingUnit
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOriginUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.UpperStarDerived
public import WeilConjectures.TraceFormula.TransverseBoundary.MonodromyDevissage
public import WeilConjectures.TraceFormula.TransverseBoundary.MonodromyPullback

/-!
# Dévissage of module complexes with finite `ℓ`-group monodromy

Let `T` be a finite discrete field of characteristic `ℓ`, `Λ = C(-, T)` and
`Φ = ProEtale.finiteCoefficientDerivedEquivalence Y T` the comparison of `D(Mod_{Λ_Y})` with the
derived category of pro-étale sheaves of `T`-modules on a connected scheme `Y`. This file
transports the étale dévissage of bounded complexes with finite `ℓ`-group monodromy
(`AlgebraicGeometry.Etale.prop_of_isBoundedFiniteEllGroupMonodromy`) along `Φ⁻¹ ∘ ν^*`: a
property of `D(Mod_{Λ_Y})` stable under isomorphisms, shifts and extensions which holds for the
unit holds for every `K` with `Φ K ≅ ν^* F'`, `F'` bounded with finite `ℓ`-group monodromy. The
constant sheaves `N_Y` of the étale dévissage are finite direct sums of the unit, `T` being a
field.

## Main results

- `CategoryTheory.Pretriangulated.prop_of_isZero_of_prop`,
  `CategoryTheory.Pretriangulated.prop_biprod`: a property stable under shifts and extensions
  contains the zero objects as soon as it contains some object, and is stable under binary
  biproducts.
- `CategoryTheory.Pretriangulated.prop_obj_of_moduleFinite`: such a property holds on the image of
  every finite-dimensional vector space under an additive functor if it holds on the image of the
  field itself.
- `AlgebraicGeometry.ProEtale.prop_of_isBoundedFiniteEllGroupMonodromy_finiteCoefficient`: the
  dévissage on `D(Mod_{Λ_Y})`, ending at the unit.
- `AlgebraicGeometry.ProEtale.finiteCoefficientDerivedEquivalenceLeftDerivedUpperStarIso`:
  `Φ_W (Lg^* K) ≅ ν^* (g^* F')` for `Φ_Y K ≅ ν^* F'`.
- `AlgebraicGeometry.ProEtale.prop_leftDerivedUpperStar_of_isBoundedFiniteEllGroupMonodromy`: the
  dévissage applied to a derived pullback `Lg^* K` to a connected scheme.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory.Pretriangulated

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]

/-- A property of objects of a pretriangulated category stable under shifts and extensions holds
for every zero object as soon as it holds for some object `X`: the rotated contractible triangle
`X ⟶ 0 ⟶ X⟦1⟧ ⟶ X⟦1⟧` is distinguished. -/
lemma prop_of_isZero_of_prop (hshift : ∀ (K : C) (n : ℤ), P K → P (K⟦n⟧))
    (hext : ∀ T ∈ distTriang C, P T.obj₁ → P T.obj₃ → P T.obj₂) {X : C} (hX : P X)
    {Z : C} (hZ : IsZero Z) : P Z :=
  P.prop_of_iso ((isZero_zero C).iso hZ)
    (hext _ (rot_of_distTriang _ (contractible_distinguished X)) hX (hshift X 1 hX))

omit [P.IsClosedUnderIsomorphisms] in
/-- A property of objects of a pretriangulated category stable under extensions is stable under
binary biproducts: the split triangle `X₁ ⟶ X₁ ⊞ X₂ ⟶ X₂ ⟶ X₁⟦1⟧` is distinguished. -/
lemma prop_biprod (hext : ∀ T ∈ distTriang C, P T.obj₁ → P T.obj₃ → P T.obj₂) {X₁ X₂ : C}
    (h₁ : P X₁) (h₂ : P X₂) : P (X₁ ⊞ X₂) :=
  hext _ (binaryBiproductTriangle_distinguished X₁ X₂) h₁ h₂

/-- Let `G` be an additive functor from vector spaces over a field `K` to a pretriangulated
category. A property stable under shifts and extensions which holds for `G K` holds for `G N` for
every finite-dimensional `N`: `N ≅ K ⊞ ⋯ ⊞ K` and `G` preserves biproducts. -/
lemma prop_obj_of_moduleFinite {K : Type*} [Field K] (G : ModuleCat K ⥤ C) [G.Additive]
    (hshift : ∀ (K : C) (n : ℤ), P K → P (K⟦n⟧))
    (hext : ∀ T ∈ distTriang C, P T.obj₁ → P T.obj₃ → P T.obj₂)
    (hunit : P (G.obj (ModuleCat.of K K))) (N : ModuleCat K) [Module.Finite K N] :
    P (G.obj N) := by
  have := preservesBinaryBiproducts_of_preservesBiproducts G
  have key (r : ℕ) : P (G.obj (ModuleCat.of K (Fin r → K))) := by
    induction r with
    | zero =>
      exact prop_of_isZero_of_prop P hshift hext hunit
        (G.map_isZero (ModuleCat.isZero_of_subsingleton _))
    | succ r ih =>
      exact P.prop_of_iso ((G.mapBiprod (ModuleCat.of K K) (ModuleCat.of K (Fin r → K))).symm ≪≫
          G.mapIso (ModuleCat.biprodIsoProd _ _ ≪≫
            (Fin.consLinearEquiv K fun _ : Fin (r + 1) ↦ K).toModuleIso))
        (prop_biprod P hext hunit ih)
  exact P.prop_of_iso (G.mapIso (Module.finBasis K N).equivFun.toModuleIso.symm) (key _)

end CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.ProEtale

variable (T : Type) [TopologicalSpace T] [Field T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

/-- The inverse of the derived finite-coefficient comparison commutes with the shifts, being
`D(Φ⁻¹)` for the exact equivalence `Φ = finiteCoefficientModEquivalence`. -/
noncomputable instance commShift_finiteCoefficientDerivedEquivalence_inverse (Y : Scheme.{u}) :
    (finiteCoefficientDerivedEquivalence Y T).inverse.CommShift ℤ :=
  inferInstanceAs (D((finiteCoefficientModEquivalence Y T).inverse).CommShift ℤ)

/-- The inverse of the derived finite-coefficient comparison is triangulated, being `D(Φ⁻¹)` for
the exact equivalence `Φ = finiteCoefficientModEquivalence`. -/
instance isTriangulated_finiteCoefficientDerivedEquivalence_inverse (Y : Scheme.{u}) :
    (finiteCoefficientDerivedEquivalence Y T).inverse.IsTriangulated :=
  inferInstanceAs (D((finiteCoefficientModEquivalence Y T).inverse).IsTriangulated)

/-- The inverse of the derived comparison `Φ` sends the unit to the unit
(`finiteCoefficientDerivedEquivalenceUnitIso`). -/
noncomputable def finiteCoefficientDerivedEquivalenceInverseUnitIso (Y : Scheme.{u}) :
    (finiteCoefficientDerivedEquivalence Y T).inverse.obj (𝟙_ _) ≅ 𝟙_ _ :=
  (finiteCoefficientDerivedEquivalence Y T).inverse.mapIso
      (finiteCoefficientDerivedEquivalenceUnitIso Y T).symm ≪≫
    ((finiteCoefficientDerivedEquivalence Y T).unitIso.app _).symm

/-- The constant sheaf at the unit, placed in degree `0`, pulled back to the pro-étale site and
transported by `Φ⁻¹`, is the unit of `D(Mod_{Λ_Y})`. -/
noncomputable def finiteCoefficientDerivedEquivalenceInverseConstantUnitIso (Y : Scheme.{u}) :
    (finiteCoefficientDerivedEquivalence Y T).inverse.obj
        (D(ν^*(Y)[ModuleCat.{u + 1} (ULift.{u + 1} T)]).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} T))).obj
              (ModuleCat.of (ULift.{u + 1} T) (ULift.{u + 1} T))))) ≅ 𝟙_ _ :=
  (finiteCoefficientDerivedEquivalence Y T).inverse.mapIso
      (((ν^*(Y)[ModuleCat.{u + 1} (ULift.{u + 1} T)]).mapDerivedCategorySingleFunctor 0).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso (comparisonUpperStarUnitIso _ Y) ≪≫
        DerivedCategory.singleFunctorObjUnitIso _) ≪≫
    finiteCoefficientDerivedEquivalenceInverseUnitIso T Y

/-- **The derived comparison commutes with pullback on complexes of étale origin**: for
`g : W ⟶ Y` and `Φ_Y K ≅ ν^* F'`, `Φ_W (Lg^* K) ≅ ν^* (g^* F')`, the étale pullback `g^*` being
exact. Combines `leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso` and
`comparisonUpperStarUpperStarIso`. -/
noncomputable def finiteCoefficientDerivedEquivalenceLeftDerivedUpperStarIso {W Y : Scheme.{u}}
    (g : W ⟶ Y)
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) Y))}
    {F' : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} T)))}
    (e : (finiteCoefficientDerivedEquivalence Y T).functor.obj K ≅
      D(ν^*(Y)[ModuleCat.{u + 1} (ULift.{u + 1} T)]).obj F') :
    (finiteCoefficientDerivedEquivalence W T).functor.obj
        (L(CondensedRing.upperStar (Profinite.continuousMapRingObj T) g).obj K) ≅
      D(ν^*(W)[ModuleCat.{u + 1} (ULift.{u + 1} T)]).obj
        (D(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} T)) g).obj F') :=
  (leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso g T).app K ≪≫
    L(ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} T)) g).mapIso e ≪≫
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} T)) g).app _ ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).app F' ≪≫
    (Functor.mapDerivedCategoryNatIso
      (comparisonUpperStarUpperStarIso (ModuleCat.{u + 1} (ULift.{u + 1} T)) g)).app F' ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm.app F'

variable (ℓ : ℕ) [Fact ℓ.Prime] [CharP T ℓ]

/-- **Dévissage of module complexes with finite `ℓ`-group monodromy**: on a connected scheme
`Y`, a property of `D(Mod_{Λ_Y})`, `Λ = C(-, T)` with `T` a finite field of characteristic `ℓ`,
stable under isomorphisms, shifts and extensions which holds for the unit holds for every `K`
with `Φ K ≅ ν^* F'`, `F'` a bounded étale complex with finite `ℓ`-group monodromy. This is the
étale dévissage `Etale.prop_of_isBoundedFiniteEllGroupMonodromy` applied to `P ∘ Φ⁻¹ ∘ ν^*`; the
constant sheaves `N_Y` are finite direct sums of the unit. -/
theorem prop_of_isBoundedFiniteEllGroupMonodromy_finiteCoefficient {Y : Scheme.{u}}
    [ConnectedSpace Y]
    (P : ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) Y))))
    [P.IsClosedUnderIsomorphisms]
    (hshift : ∀ K (n : ℤ), P K → P (K⟦n⟧))
    (hext : ∀ Tr ∈ distTriang _, P Tr.obj₁ → P Tr.obj₃ → P Tr.obj₂)
    (hunit : P (𝟙_ _))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) Y)))
    (F' : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} T))))
    (hF' : Etale.IsBoundedFiniteEllGroupMonodromy ℓ F')
    (e : (finiteCoefficientDerivedEquivalence Y T).functor.obj K ≅
      D(ν^*(Y)[ModuleCat.{u + 1} (ULift.{u + 1} T)]).obj F') :
    P K := by
  let G := D(ν^*(Y)[ModuleCat.{u + 1} (ULift.{u + 1} T)]) ⋙
    (finiteCoefficientDerivedEquivalence Y T).inverse
  refine P.prop_of_iso ((finiteCoefficientDerivedEquivalence Y T).unitIso.app K ≪≫
    (finiteCoefficientDerivedEquivalence Y T).inverse.mapIso e).symm ?_
  refine Etale.prop_of_isBoundedFiniteEllGroupMonodromy ℓ ⟨1, ?_⟩ (P.inverseImage G)
    (fun L n hL ↦ P.prop_of_iso ((G.commShiftIso n).app L).symm (hshift _ n hL))
    (fun Tr hTr h₁ h₃ ↦ hext _ (G.map_distinguished Tr hTr) h₁ h₃) ?_ F' hF'
  · exact ULift.down_injective (by simp)
  · intro N _ _
    exact Pretriangulated.prop_obj_of_moduleFinite (P.inverseImage G)
      (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} T)) ⋙
        DerivedCategory.singleFunctor _ 0)
      (fun L n hL ↦ P.prop_of_iso ((G.commShiftIso n).app L).symm (hshift _ n hL))
      (fun Tr hTr h₁ h₃ ↦ hext _ (G.map_distinguished Tr hTr) h₁ h₃)
      (P.prop_of_iso (finiteCoefficientDerivedEquivalenceInverseConstantUnitIso T Y).symm hunit)
      N

/-- **Dévissage of pulled back module complexes**: for `g : W ⟶ Y` with `W` connected and
`Φ_Y K ≅ ν^* F'`, `F'` bounded with finite `ℓ`-group monodromy, a property of `D(Mod_{Λ_W})`
stable under isomorphisms, shifts and extensions which holds for the unit holds for `Lg^* K`
(`finiteCoefficientDerivedEquivalenceLeftDerivedUpperStarIso`,
`Etale.IsBoundedFiniteEllGroupMonodromy.mapDerivedCategoryUpperStar`). -/
theorem prop_leftDerivedUpperStar_of_isBoundedFiniteEllGroupMonodromy {W Y : Scheme.{u}}
    [ConnectedSpace W] (g : W ⟶ Y)
    (P : ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) W))))
    [P.IsClosedUnderIsomorphisms]
    (hshift : ∀ K (n : ℤ), P K → P (K⟦n⟧))
    (hext : ∀ Tr ∈ distTriang _, P Tr.obj₁ → P Tr.obj₃ → P Tr.obj₂)
    (hunit : P (𝟙_ _))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) Y)))
    (F' : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} T))))
    (hF' : Etale.IsBoundedFiniteEllGroupMonodromy ℓ F')
    (e : (finiteCoefficientDerivedEquivalence Y T).functor.obj K ≅
      D(ν^*(Y)[ModuleCat.{u + 1} (ULift.{u + 1} T)]).obj F') :
    P (L(CondensedRing.upperStar (Profinite.continuousMapRingObj T) g).obj K) :=
  prop_of_isBoundedFiniteEllGroupMonodromy_finiteCoefficient T ℓ P hshift hext hunit _ _
    (hF'.mapDerivedCategoryUpperStar g)
    (finiteCoefficientDerivedEquivalenceLeftDerivedUpperStarIso T g e)

end AlgebraicGeometry.ProEtale
