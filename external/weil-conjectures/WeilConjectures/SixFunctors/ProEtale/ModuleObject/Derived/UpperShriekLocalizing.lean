/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.BoundedEssentiallySmall
public import WeilConjectures.CategoryTheory.DerivedCategory.Coproducts
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.CategoryTheory.Triangulated.BrownRepresentability.RightAdjoint
public import WeilConjectures.CategoryTheory.Triangulated.CompactObjExtension
public import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosureGeneration
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ConstructibleEmbedding
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructibleEllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible

/-!
# The exceptional inverse image on `Loc(Dᵇc)`, `ℓ`-adic coefficients

Let `Λ` be a commutative condensed ring. For a scheme `X` the localizing closure
`Loc(Dᵇc(X)⟦Λ⟧)` (blueprint `definition-localizing-subcategory`) is the smallest triangulated
subcategory of `D(X_proét, Λ_X)` (module objects over `Λ_X = p_X^* Λ`) containing the bounded
constructible complexes `Dᵇc(X)⟦Λ⟧` and closed under direct sums
(`AlgebraicGeometry.ProEtale.CondensedRing.localizingBoundedConstructible`). For the `ℓ`-adic
coefficient rings `Λ = 𝒪_E, E, ℚ̄_ℓ` (`ℤ_ℓ` and `ℚ_ℓ` being the case `E = ℚ_ℓ`), one has
`Dctf(X, Λ) = Dᵇc(X, Λ)`, so this is the blueprint's `Loc(Dctf(X, Λ))`.

For a compactification `c = (X ⟶[j] X̄ ⟶[p] Y)` of `f : X ⟶ Y` such that `Rf_!(c)⟦Λ⟧` maps
`Loc(Dᵇc(X)⟦Λ⟧)` into `Loc(Dᵇc(Y)⟦Λ⟧)`, its restriction is the functor
`Rf_! : Loc(Dᵇc(X)⟦Λ⟧) ⥤ Loc(Dᵇc(Y)⟦Λ⟧)`
(`AlgebraicGeometry.ProEtale.CondensedRing.rightDerivedLowerShriekLocalizing`). Under the
hypotheses of Brown representability (blueprint `lemma-hypotheses-brown-representability`) and the
properties of `Rf_!(c)` of blueprint `proposition-construction-independence-rf-shriek`, it has an
exact right adjoint `f^!`, which preserves direct sums and is unique up to unique isomorphism
(`AlgebraicGeometry.ProEtale.CondensedRing.exists_rightAdjoint_rightDerivedLowerShriekLocalizing`,
blueprint `theorem-existence-exceptional-inverse-image`). This is uniform in `Λ`.

For the three families of `ℓ`-adic coefficient rings, schemes separated of finite type over a
field `k` in which `ℓ` is invertible and which is finite or separably closed (so that
`cd_ℓ(k)` is finite; without this, the compact generation fails, e.g. for `k = ℝ`), the two
inputs are the theorems

| `Λ` | `lemma-hypotheses-brown-representability` |
`proposition-construction-independence-rf-shriek` |
| --- | --- | --- |
| `E` | `compactlyGenerates_continuousMapRingObj` | `lowerShriek_continuousMapRingObj` |
| `𝒪_E` | `compactlyGenerates_padicIntegersRingObj` | `lowerShriek_padicIntegersRingObj` |
| `ℚ̄_ℓ` | `compactlyGenerates_padicAlgClRingObj` | `lowerShriek_padicAlgClRingObj` |

(all in the namespace `AlgebraicGeometry.ProEtale.CondensedRing`, in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizingEllAdic`), and the
existence theorem follows. The finite coefficient rings are treated in
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing`.

## The formal reductions

For `lemma-hypotheses-brown-representability`, on a separated finite-type (hence noetherian)
`k`-scheme `X`: `Loc(Dᵇc(X)⟦Λ⟧)` is idempotent complete, as is any pretriangulated category with
countable coproducts (`ObjectProperty.isIdempotentComplete_localizingClosure`); `Dᵇc(X)⟦Λ⟧` is
stable under shifts, so its objects detect zero objects of `Loc(Dᵇc(X)⟦Λ⟧)`
(`ObjectProperty.isZero_of_forall_eq_zero_localizingClosure`); and it is essentially small, its
objects being iterated extensions of shifted constructible sheaves
(`exists_skeleton_boundedConstructible`). What remains is the compactness of the bounded
constructible complexes in `Loc(Dᵇc(X)⟦Λ⟧)` (`compactlyGenerates_of_isCompactObj`), which reduces
to that of the constructible sheaves.

For `proposition-construction-independence-rf-shriek`, with `X̄` noetherian: `j_!` is exact and
preserves direct sums, so it maps `Dᵇc` into `Dᵇc`, as it maps constructible sheaves to
constructible sheaves (`isConstructibleModuleObject_openImmersionLowerShriek_obj`), and then
`Loc` into `Loc` (`localizingBoundedConstructible_mapDerivedCategory_openImmersionLowerShriek_obj`);
the composite `Rp_* ∘ j_!` then has the required properties as soon as `Rp_*` does
(`lowerShriekLocalizingHypotheses_of_properLowerStarHypotheses`).
-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Abelian Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- Blueprint `definition-localizing-subcategory`: the localizing closure `Loc(Dᵇc(X)⟦Λ⟧)`, the
smallest triangulated subcategory of `D(X_proét, Λ_X)` closed under isomorphisms and direct sums
which contains the bounded constructible complexes. For the `ℓ`-adic coefficient rings these are the
blueprint's `Dctf(X, Λ)`. -/
noncomputable abbrev localizingBoundedConstructible (X : Scheme.{u}) :
    ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :=
  (boundedConstructible (condensedRingObj Λ X)).localizingClosure

/-- The category `Loc(Dᵇc(X)⟦Λ⟧)`, a full subcategory of `D(X_proét, Λ_X)`. It is
pretriangulated and has direct sums. -/
abbrev LocalizingBoundedConstructible (X : Scheme.{u}) : Type _ :=
  (localizingBoundedConstructible Λ X).FullSubcategory

/-- The derived category `D(X_proét, Λ_X)` of module objects has direct sums. -/
instance hasCoproducts_derivedCategory (X : Scheme.{u}) :
    HasCoproducts.{u + 1} (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) := by
  intro J
  have : HasColimitsOfSize.{u + 1, u + 1}
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
    IsGrothendieckAbelian.hasColimits _
  have : HasColimitsOfShape (Discrete J)
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
    HasColimitsOfSize.has_colimits_of_shape _
  exact DerivedCategory.hasColimitsOfShape_discrete J

section General

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- The properties of the compact-support direct image `Rf_!(c)⟦Λ⟧ = Rp_* ∘ j_!` along a
compactification `c = (X ⟶[j] X̄ ⟶[p] Y)` of blueprint
`proposition-construction-independence-rf-shriek`: it maps `Loc(Dᵇc(X)⟦Λ⟧)` into `Loc(Dᵇc(Y)⟦Λ⟧)`
and `Dᵇc(X)⟦Λ⟧` into `Dᵇc(Y)⟦Λ⟧`, and its restriction to `Loc(Dᵇc(X)⟦Λ⟧)` preserves direct sums. -/
def LowerShriekLocalizingHypotheses : Prop :=
  (∀ K, localizingBoundedConstructible Λ X K →
    localizingBoundedConstructible Λ Y ((rightDerivedLowerShriekOfCompactification Λ c).obj K)) ∧
  (∀ K, boundedConstructible (condensedRingObj Λ X) K →
    boundedConstructible (condensedRingObj Λ Y)
      ((rightDerivedLowerShriekOfCompactification Λ c).obj K)) ∧
  ∀ J : Type (u + 1), PreservesColimitsOfShape (Discrete J)
    ((localizingBoundedConstructible Λ X).ι ⋙ rightDerivedLowerShriekOfCompactification Λ c)

variable {Λ c} (hc : LowerShriekLocalizingHypotheses Λ c)

/-- The compact-support direct image `Rf_! : Loc(Dᵇc(X)⟦Λ⟧) ⥤ Loc(Dᵇc(Y)⟦Λ⟧)` attached to a
compactification `c` of `f`: the restriction of `Rf_!(c)⟦Λ⟧`. -/
noncomputable abbrev rightDerivedLowerShriekLocalizing :
    LocalizingBoundedConstructible Λ X ⥤ LocalizingBoundedConstructible Λ Y :=
  ObjectProperty.localizingClosureLift _ _ (rightDerivedLowerShriekOfCompactification Λ c) hc.1

/-- `Rf_!` on the localizing closures preserves direct sums (blueprint
`proposition-construction-independence-rf-shriek`). -/
instance (J : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete J) (rightDerivedLowerShriekLocalizing hc) :=
  have := hc.2.2 J
  ObjectProperty.preservesColimitsOfShape_localizingClosureLift _ _ _ _ J

omit [IsCommMonObj Λ] in
/-- Blueprint `theorem-existence-exceptional-inverse-image`, uniformly in the coefficient ring `Λ`:
if `Dᵇc(X)⟦Λ⟧` and `Dᵇc(Y)⟦Λ⟧` compactly generate their localizing closures (blueprint
`lemma-hypotheses-brown-representability`) and `Rf_!(c)⟦Λ⟧` has the properties of blueprint
`proposition-construction-independence-rf-shriek`, then the coproduct-preserving functor
`Rf_! : Loc(Dᵇc(X)⟦Λ⟧) ⥤ Loc(Dᵇc(Y)⟦Λ⟧)` has a right adjoint `f^!`, which commutes with shifts
compatibly with the adjunction, is exact (triangulated), preserves direct sums and is unique up
to unique isomorphism compatible with the adjunction. -/
theorem exists_rightAdjoint_rightDerivedLowerShriekLocalizing
    (hX : (boundedConstructible (condensedRingObj Λ X)).CompactlyGeneratesLocalizingClosure)
    (hY : (boundedConstructible (condensedRingObj Λ Y)).CompactlyGeneratesLocalizingClosure) :
    ∃ (G : LocalizingBoundedConstructible Λ Y ⥤ LocalizingBoundedConstructible Λ X)
      (adj : rightDerivedLowerShriekLocalizing hc ⊣ G) (_ : G.CommShift ℤ),
      adj.CommShift ℤ ∧ G.IsTriangulated ∧
      (∀ J : Type (u + 1), PreservesColimitsOfShape (Discrete J) G) ∧
      ∀ (G' : LocalizingBoundedConstructible Λ Y ⥤ LocalizingBoundedConstructible Λ X)
        (adj' : rightDerivedLowerShriekLocalizing hc ⊣ G'),
        ∃! e : G ≅ G', ∀ N, (rightDerivedLowerShriekLocalizing hc).map (e.hom.app N) ≫
          adj'.counit.app N = adj.counit.app N :=
  have := hc.2.2
  ObjectProperty.exists_rightAdjoint_localizingClosureLift _ _ _ _ hX hY hc.2.1

end General

/-! ### Reduction to the coefficient-specific inputs -/

section Reduction

/-- The bounded constructible complexes are stable under shifts: `Hᵃ(K⟦n⟧) ≅ Hⁿ⁺ᵃ(K)`. -/
instance isStableUnderShift_boundedConstructible (X : Scheme.{u}) :
    (boundedConstructible (condensedRingObj Λ X)).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun K hK ↦ ⟨DerivedCategory.TStructure.t.bounded.le_shift n K hK.1,
    fun a ↦ IsConstructibleModuleObject.of_iso
      (((DerivedCategory.homologyFunctor _ 0).shiftIso n a (n + a) rfl).app K).symm (hK.2 (n + a))⟩⟩

/-- Constructibility of module objects is invariant under isomorphisms. -/
instance isClosedUnderIsomorphisms_isConstructibleModuleObject (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms
      (IsConstructibleModuleObject (condensedRingObj Λ X)) where
  of_iso e h := IsConstructibleModuleObject.of_iso e h

/-- Blueprint `lemma-hypotheses-brown-representability--5` (constructible hearts): the constructible
module objects on a noetherian scheme are essentially small. A constructible sheaf embeds into a
finite product of pushforwards of pullbacks of finitely presented module objects, which form a set
(`essentiallySmall_isConstructibleModuleObject_of_noetherianSpace`). -/
theorem essentiallySmall_isConstructibleModuleObject (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X] :
    ObjectProperty.EssentiallySmall.{u + 1}
      (IsConstructibleModuleObject (condensedRingObj Λ X)) :=
  essentiallySmall_isConstructibleModuleObject_of_noetherianSpace Λ X

/-- Blueprint `lemma-hypotheses-brown-representability--5`: the bounded constructible complexes on a
noetherian scheme are essentially small: a bounded complex with constructible cohomology is obtained
from its shifted cohomology sheaves by finitely many extensions
(`DerivedCategory.essentiallySmall_bounded_inf`), and the constructible sheaves are essentially
small (`essentiallySmall_isConstructibleModuleObject`). -/
theorem exists_skeleton_boundedConstructible (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X] :
    ∃ (ι : Type (u + 1)) (S : ι → DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X)
      Ab.{u + 1}) (condensedRingObj Λ X))), (∀ i, boundedConstructible _ (S i)) ∧
      ∀ K, boundedConstructible (condensedRingObj Λ X) K → ∃ i, Nonempty (S i ≅ K) := by
  have := essentiallySmall_isConstructibleModuleObject Λ X
  have : ObjectProperty.EssentiallySmall.{u + 1} (boundedConstructible (condensedRingObj Λ X)) :=
    DerivedCategory.essentiallySmall_bounded_inf _
  obtain ⟨Q, _, hQ, hle⟩ := ObjectProperty.EssentiallySmall.exists_small_le
    (boundedConstructible (condensedRingObj Λ X))
  refine ⟨Shrink.{u + 1} (Subtype Q), fun i ↦ ((equivShrink _).symm i).1,
    fun i ↦ hQ _ ((equivShrink _).symm i).2, fun K hK ↦ ?_⟩
  obtain ⟨K', hK', ⟨e⟩⟩ := hle K hK
  exact ⟨equivShrink _ ⟨K', hK'⟩, ⟨by simpa using e.symm⟩⟩

/-- The formal part of blueprint `lemma-hypotheses-brown-representability`: on a noetherian scheme
`X`, `Loc(Dᵇc(X)⟦Λ⟧)` is idempotent complete (`lemma-hypotheses-brown-representability`), and if the
bounded constructible complexes are compact in it, they compactly generate it
(`lemma-hypotheses-brown-representability`). -/
theorem compactlyGenerates_of_isCompactObj (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (h : ∀ K : LocalizingBoundedConstructible Λ X,
      boundedConstructible (condensedRingObj Λ X) K.obj → BrownRepresentability.IsCompactObj K) :
    (boundedConstructible (condensedRingObj Λ X)).CompactlyGeneratesLocalizingClosure ∧
      IsIdempotentComplete (LocalizingBoundedConstructible Λ X) :=
  ⟨.of_isStableUnderShift (exists_skeleton_boundedConstructible Λ X) h,
    ObjectProperty.isIdempotentComplete_localizingClosure _⟩

/-- A constructible sheaf `M`, placed in degree `0`, as an object of `Loc(Dᵇc(X)⟦Λ⟧)`. -/
noncomputable abbrev singleLocalizingBoundedConstructible (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsConstructibleModuleObject (condensedRingObj Λ X) M) :
    LocalizingBoundedConstructible Λ X :=
  ⟨(DerivedCategory.singleFunctor _ 0).obj M, ObjectProperty.le_localizingClosure _ _
    (boundedConstructible_singleFunctor_obj Λ X 0 M hM)⟩

omit [IsCommMonObj Λ] in
/-- Blueprint `theorem-compactness-rational-coefficients`: if the constructible sheaves are compact
objects of `Loc(Dᵇc(X)⟦Λ⟧)`, then so are all bounded constructible complexes. Compact objects
are stable under shifts and extensions, and a bounded constructible complex is an iterated
extension of shifted constructible sheaves
(`DerivedCategory.exists_iteratedExtensions_of_bounded`). -/
theorem isCompactObj_of_isCompactObj_singleLocalizingBoundedConstructible (X : Scheme.{u})
    (h : ∀ M hM, BrownRepresentability.IsCompactObj (singleLocalizingBoundedConstructible Λ X M hM))
    (K : LocalizingBoundedConstructible Λ X)
    (hK : boundedConstructible (condensedRingObj Λ X) K.obj) :
    BrownRepresentability.IsCompactObj K := by
  let P := IsConstructibleModuleObject (condensedRingObj Λ X)
  have hle : DerivedCategory.singleObjects P ≤ localizingBoundedConstructible Λ X := by
    rintro L ⟨n, M, hM, ⟨e⟩⟩
    exact ObjectProperty.le_localizingClosure _ _ (ObjectProperty.prop_of_iso _ e.symm
      (boundedConstructible_singleFunctor_obj Λ X n M hM))
  have hsingle (L : LocalizingBoundedConstructible Λ X)
      (hL : DerivedCategory.singleObjects P L.obj) :
      BrownRepresentability.IsCompactObj L := by
    obtain ⟨n, M, hM, ⟨e⟩⟩ := hL
    let S := singleLocalizingBoundedConstructible Λ X M hM
    exact ((h M hM).shift (-n)).of_iso
      ((localizingBoundedConstructible Λ X).fullyFaithfulι.preimageIso
      (e ≪≫ (((DerivedCategory.singleFunctors _).shiftIso (-n) n 0 (by simp)).app M).symm ≪≫
        (((localizingBoundedConstructible Λ X).ι.commShiftIso (-n)).app S).symm))
  obtain ⟨d, hd⟩ := DerivedCategory.exists_iteratedExtensions_of_bounded P K.obj hK.1 hK.2
  clear hK
  induction d generalizing K with
  | zero => exact hsingle K hd
  | succ d ih =>
    obtain ⟨Y, Z, f, g, k, hT, hY, hZ⟩ := hd
    have hY' := DerivedCategory.iteratedExtensions_le P hle d Y hY
    exact ObjectProperty.FullSubcategory.isCompactObj_of_distTriang _ (Y := ⟨Y, hY'⟩)
      (Z := ⟨Z, hle Z hZ⟩) f g k hT (ih ⟨Y, hY'⟩ hY) (hsingle ⟨Z, hle Z hZ⟩ hZ)

/-- Blueprint `proposition-proper-direct-image-extension-zero` (extension by zero): for an open
immersion `j : U ⟶ X` into a noetherian scheme, `j_!` maps `Dᵇc(U)⟦Λ⟧` into `Dᵇc(X)⟦Λ⟧`: `j_!` is
exact, so `Hⁿ(j_! K) ≅ j_! Hⁿ(K)`. -/
theorem boundedConstructible_mapDerivedCategory_openImmersionLowerShriek_obj {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [TopologicalSpace.NoetherianSpace X]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U)))
    (hK : boundedConstructible (condensedRingObj Λ U) K) :
    boundedConstructible (condensedRingObj Λ X) ((D((j)_!open⟦Λ⟧)).obj K) := by
  let e (n : ℤ) := ((j)_!open⟦Λ⟧.mapDerivedCategoryHomologyFunctorIso n).app K
  obtain ⟨⟨a, b, hab⟩, hK⟩ := (mem_boundedConstructible_iff _ K).1 hK
  refine (mem_boundedConstructible_iff _ _).2 ⟨⟨a, b, fun i hi ↦ ?_⟩, fun n ↦ ?_⟩
  · exact (Functor.map_isZero (j)_!open⟦Λ⟧ (hab i hi)).of_iso (e i).symm
  · exact IsConstructibleModuleObject.of_iso (e n)
      (isConstructibleModuleObject_openImmersionLowerShriek_obj Λ j _ (hK n))

/-- The properties of the derived direct image `Rp_*` along a proper morphism `p` used in
blueprint `proposition-construction-independence-rf-shriek`: it maps `Dᵇc(Z)⟦Λ⟧` into `Dᵇc(Y)⟦Λ⟧`
(blueprint `proposition-proper-direct-image-constructible-complexes`) and its restriction to
`Loc(Dᵇc(Z)⟦Λ⟧)` preserves direct sums (blueprint
`proposition-proper-direct-image-extension-zero`). -/
def ProperLowerStarHypotheses {Z Y : Scheme.{u}} (p : Z ⟶ Y) : Prop :=
  (∀ K, boundedConstructible (condensedRingObj Λ Z) K →
    boundedConstructible (condensedRingObj Λ Y) ((R((p)_*⟦Λ⟧)).obj K)) ∧
  ∀ J : Type (u + 1), PreservesColimitsOfShape (Discrete J)
    ((localizingBoundedConstructible Λ Z).ι ⋙ R((p)_*⟦Λ⟧))

/-- The extension by zero `j_!` along an open immersion preserves direct sums. -/
instance preservesColimitsOfShape_mapDerivedCategory_openImmersionLowerShriek {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (J : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete J) D((j)_!open⟦Λ⟧) := by
  have (T : Scheme.{u}) : HasColimitsOfSize.{u + 1, u + 1}
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) :=
    IsGrothendieckAbelian.hasColimits _
  have : HasColimitsOfShape (Discrete J)
      (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) :=
    HasColimitsOfSize.has_colimits_of_shape _
  have : HasColimitsOfShape (Discrete J)
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
    HasColimitsOfSize.has_colimits_of_shape _
  have : PreservesColimitsOfSize.{u + 1, u + 1} (j)_!open⟦Λ⟧ :=
    (openImmersionLowerShriekUpperStarAdjunction Λ j).leftAdjoint_preservesColimits
  exact Functor.preservesColimitsOfShape_mapDerivedCategory _ J

/-- Blueprint `proposition-proper-direct-image-extension-zero` (extension by zero, formal part): for
an open immersion `j : U ⟶ X` into a noetherian scheme, `j_!` maps `Loc(Dᵇc(U)⟦Λ⟧)` into
`Loc(Dᵇc(X)⟦Λ⟧)`. -/
theorem localizingBoundedConstructible_mapDerivedCategory_openImmersionLowerShriek_obj
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [TopologicalSpace.NoetherianSpace X]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U)))
    (hK : localizingBoundedConstructible Λ U K) :
    localizingBoundedConstructible Λ X ((D((j)_!open⟦Λ⟧)).obj K) :=
  ObjectProperty.localizingClosure_obj_of_le _ _ _ (fun K hK ↦ ObjectProperty.le_localizingClosure
    _ _ (boundedConstructible_mapDerivedCategory_openImmersionLowerShriek_obj Λ j K hK)) K hK

/-- Blueprint `proposition-construction-independence-rf-shriek`, reduced to its inputs: for a
compactification `c = (X ⟶[j] X̄ ⟶[p] Y)` with `X̄` noetherian, if `Rp_*` has the properties
`ProperLowerStarHypotheses`, then `Rf_!(c) = Rp_* ∘ j_!` has the properties
`LowerShriekLocalizingHypotheses`: each factor maps `Dᵇc` into `Dᵇc` and its restriction to the
localizing closures preserves direct sums, hence so does the composite, which therefore maps
`Loc(Dᵇc(X)⟦Λ⟧)` into `Loc(Dᵇc(Y)⟦Λ⟧)`. -/
theorem lowerShriekLocalizingHypotheses_of_properLowerStarHypotheses {X Y : Scheme.{u}}
    {f : X ⟶ Y} (c : Compactification f) [TopologicalSpace.NoetherianSpace c.Z]
    (hp : ProperLowerStarHypotheses Λ c.g) : LowerShriekLocalizingHypotheses Λ c := by
  have h₂ (K) (hK : boundedConstructible (condensedRingObj Λ X) K) :
      boundedConstructible (condensedRingObj Λ Y)
        ((rightDerivedLowerShriekOfCompactification Λ c).obj K) :=
    hp.1 _ (boundedConstructible_mapDerivedCategory_openImmersionLowerShriek_obj Λ c.i K hK)
  have h₃ (J : Type (u + 1)) : PreservesColimitsOfShape (Discrete J)
      ((localizingBoundedConstructible Λ X).ι ⋙ rightDerivedLowerShriekOfCompactification Λ c) := by
    have := hp.2 J
    let L := ObjectProperty.localizingClosureLift _ _ D((c.i)_!open⟦Λ⟧)
      (localizingBoundedConstructible_mapDerivedCategory_openImmersionLowerShriek_obj Λ c.i)
    exact preservesColimitsOfShape_of_natIso
      (F := L ⋙ (localizingBoundedConstructible Λ c.Z).ι ⋙ R((c.g)_*⟦Λ⟧))
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight
        (ObjectProperty.localizingClosureLiftCompιIso _ _ _ _) _ ≪≫ Functor.associator _ _ _)
  exact ⟨ObjectProperty.localizingClosure_obj_of_le _ _ _
    (fun K hK ↦ ObjectProperty.le_localizingClosure _ _ (h₂ K hK)), h₂, h₃⟩

end Reduction

end AlgebraicGeometry.ProEtale.CondensedRing
