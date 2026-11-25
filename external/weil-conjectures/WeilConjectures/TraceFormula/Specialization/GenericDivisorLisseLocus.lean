/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.NormalSchemeOpen
public import WeilConjectures.ConstructibleSheaf.GenericConstancy
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.QuotPowStratification
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EllGroupMonodromyDevissage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOrigin
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldTransport
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorFiniteGeneric
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorGenericPoint
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorShrink
import WeilConjectures.Tactic.ExactModProofs

/-!

# Shrinking around a generic point of a divisor to the lisse locus

Let `X` be normal, `Z = V(h)` a principal divisor with complement `j : X ∖ Z ⟶ X`, `ζ` a generic
point of `Z`, and `F` a bounded constructible complex of `𝔽_E`-module objects on `X ∖ Z`. The
complex `F` comes from a bounded constructible étale complex `F₀`, whose homology sheaves are
finite locally constant on a dense open `D` of `X ∖ Z`. Since `𝒪_{X,ζ}` is a discrete valuation
ring, some open neighbourhood `V` of `ζ` in `X` satisfies `V ∖ Z ⊆ D`
(`ProEtale.CondensedRing.exists_opens_inter_subset_image`). Restricting everything to `V`, the
vanishing of `Le^* Ψ_X(j_! F)` near `ζ` reduces to the case where the étale model of `F` has
finite locally constant homology on all of `X ∖ Z`
(`ProEtale.CondensedRing.exists_opens_lisse_reduction`).

## Main results

- `AlgebraicGeometry.Scheme.Stratification.isFiniteLocallyConstantSheaf_upperStar_interiorUnion`:
  a sheaf finite locally constant on the strata of a stratification is finite locally constant on
  the union of the interiors of the strata.
- `ProEtale.CondensedRing.exists_opens_inter_subset_image`: a dense open of `X ∖ V(h)` contains
  `V ∖ V(h)` for an open neighbourhood `V` of a generic point of `V(h)`.
- `ProEtale.CondensedRing.exists_isPullback_overRestrictι_comap`: the complement of
  `V(g^* I)` in an open `V` of `X` is the base change of the complement of `V(I)`.
- `ProEtale.CondensedRing.exists_opens_lisse_reduction`: the reduction of the generic vanishing
  along a divisor to complexes with finite locally constant homology.

-/

@[expose] public section

universe u u'

open CategoryTheory Limits Topology TopologicalSpace

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.Scheme

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA] {X : Scheme.{u}}

/-- A sheaf which is finite locally constant on every stratum of a stratification is finite
locally constant on the union of the interiors of the strata: on the interior of a stratum it is
the pullback of the sheaf along a morphism with image in the stratum. -/
theorem Stratification.isFiniteLocallyConstantSheaf_upperStar_interiorUnion
    (S : Stratification X) (F : Sheaf X.smallEtaleTopology A)
    (hS : ∀ i, IsFiniteLocallyConstantSheaf ((Etale.upperStar A (S.immersion i)).obj F)) :
    IsFiniteLocallyConstantSheaf ((Etale.upperStar A S.interiorUnion.ι).obj F) := by
  have h (i : ULift.{u} (Fin S.n)) : IsFiniteLocallyConstantSheaf
      ((Etale.upperStar A (S.interiorUnionCover.f i)).obj
        ((Etale.upperStar A S.interiorUnion.ι).obj F)) := by
    have := hS i.down
    have h' : IsFiniteLocallyConstantSheaf
        ((Etale.upperStar A (S.interiorOpens i.down).ι).obj F) := by
      refine IsFiniteLocallyConstantSheaf.upperStar_of_range_subset _ (S.immersion i.down) ?_ F
      rw [Scheme.Opens.range_ι, S.range_immersion]
      exact interior_subset
    refine IsFiniteLocallyConstantSheaf.of_iso
      (F := (Etale.upperStar A (S.interiorOpens i.down).ι).obj F) ?_
    exact eqToIso (congrArg (fun m ↦ (Etale.upperStar A m).obj F)
      (Scheme.homOfLE_ι X (le_iSup S.interiorOpens i.down)).symm) ≪≫
      (Etale.upperStarComp A (S.interiorUnionCover.f i) S.interiorUnion.ι).app F
  exact IsFiniteLocallyConstantSheaf.of_openCover S.interiorUnionCover _

/-- Pulling a complex back into the interiors of its lisse strata gives lisse homology. -/
private theorem Stratification.isFiniteLocallyConstantSheaf_homology_mapDerivedCategory_upperStar
    (S : Stratification X) {Y : Scheme.{u}} (g : Y ⟶ X)
    (hg : Set.range g.base ⊆ Set.range S.interiorUnion.ι.base)
    (F : DerivedCategory (Sheaf X.smallEtaleTopology A)) (n : ℤ)
    (hS : ∀ i, IsFiniteLocallyConstantSheaf ((Etale.upperStar A (S.immersion i)).obj
      ((DerivedCategory.homologyFunctor _ n).obj F))) :
    IsFiniteLocallyConstantSheaf ((DerivedCategory.homologyFunctor _ n).obj
      (D(Etale.upperStar A g).obj F)) := by
  have := S.isFiniteLocallyConstantSheaf_upperStar_interiorUnion _ hS
  have := IsFiniteLocallyConstantSheaf.upperStar_of_range_subset g S.interiorUnion.ι hg
    ((DerivedCategory.homologyFunctor _ n).obj F)
  exact IsFiniteLocallyConstantSheaf.of_iso
    (F := (Etale.upperStar A g).obj ((DerivedCategory.homologyFunctor _ n).obj F))
    ((Functor.mapDerivedCategoryHomologyFunctorIso (Etale.upperStar A g) n).app F)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Geometry

variable {k : Type u} [Field k] {X : Over (Spec (.of k))}

/-- **The complement of `V(g^* I)` in an open `V` is a base change**: for an open `V` of `X`, the
open immersion of the complement of `V(g^* I)` in `V`, `g : V ⟶ X`, is the base change along `g`
of the open immersion of the complement of `V(I)` in `X`. -/
lemma exists_isPullback_overRestrictι_comap (I : X.left.IdealSheafData) (V : X.left.Opens) :
    ∃ w : overRestrict (overRestrict X V) (I.comap (overRestrictι X V).left).support.compl ⟶
        overRestrict X I.support.compl,
      IsPullback w
        (overRestrictι (overRestrict X V) (I.comap (overRestrictι X V).left).support.compl)
        (overRestrictι X I.support.compl) (overRestrictι X V) := by
  have hO : (I.comap (overRestrictι X V).left).support.compl =
      (overRestrictι X V).left ⁻¹ᵁ I.support.compl := by
    ext1
    simp [Scheme.IdealSheafData.support_comap]
  generalize (I.comap (overRestrictι X V).left).support.compl = O at hO ⊢
  subst hO
  exact ⟨_, isPullback_overRestrictInterι V I.support.compl⟩

variable [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]

/-- **Dense opens of the complement of a divisor near a generic point** (`X` normal): a dense open
`D` of `X ∖ V(h)` contains `V ∖ V(h)` for some open neighbourhood `V` of a generic point `ζ` of
`V(h)`. Take for `V` the complement of the closure of `(X ∖ V(h)) ∖ D`: this closure does not
contain `ζ`, since otherwise `(X ∖ V(h)) ∖ D` would contain the generic point of `X`
(`genericPoint_mem_of_mem_closure`), which lies in the nonempty open `D`. -/
theorem exists_opens_inter_subset_image (hX : IsNormalScheme X.left) {h : Γ(X.left, ⊤)}
    (hh : h ≠ 0) {I : X.left.IdealSheafData}
    (hI : I = IdealSheafData.ofIdealTop (Ideal.span {h})) (ζ : (centre X I).left)
    (hζ : closure {ζ} ∈ irreducibleComponents (centre X I).left)
    (D : (overRestrict X I.support.compl).left.Opens)
    (hD : Dense (D : Set (overRestrict X I.support.compl).left)) :
    ∃ V : X.left.Opens, I.subschemeι ζ ∈ V ∧
      (V : Set X.left) ∩ (I.support.compl : Set X.left) ⊆
        (overRestrictι X I.support.compl).left.base '' D := by
  have := hX.1
  set ι := (overRestrictι X I.support.compl).left
  have hιr : Set.range ι.base = (I.support.compl : Set X.left) := range_overRestrictι X _
  set S := ι.base '' D
  have hS : IsOpen S := ι.isOpenEmbedding.isOpenMap _ D.isOpen
  set R := (I.support.compl : Set X.left) \ S
  refine ⟨⟨(closure R)ᶜ, isClosed_closure.isOpen_compl⟩, fun hζR ↦ ?_, ?_⟩
  · have hη : genericPoint X.left ∈ R := by
      refine genericPoint_mem_of_mem_closure hX hh hI ζ hζ (R := R) Set.sdiff_subset ?_ hζR
      rintro y ⟨hyR, hyO⟩
      refine ⟨hyO, fun hyS ↦ ?_⟩
      obtain ⟨w, hwS, hwR⟩ := mem_closure_iff.1 hyR S hS hyS
      exact hwR.2 hwS
    obtain ⟨u, -⟩ : genericPoint X.left ∈ Set.range ι.base := hιr ▸ hη.1
    have : Nonempty (overRestrict X I.support.compl).left := ⟨u⟩
    obtain ⟨d, hd⟩ := hD.nonempty
    exact hη.2 (((genericPoint_spec X.left).mem_open_set_iff hS).2 ⟨_, trivial, d, hd, rfl⟩)
  · rintro y ⟨hyR, hyO⟩
    by_contra hyS
    exact hyR (subset_closure ⟨hyO, hyS⟩)

/-- A dense open in the divisor complement contains the complement in a neighbourhood of
its generic point, together with the cartesian comparison of the two complements. -/
private lemma exists_opens_pullback_range_subset (hX : IsNormalScheme X.left) {h : Γ(X.left, ⊤)}
    (hh : h ≠ 0) {I : X.left.IdealSheafData}
    (hI : I = IdealSheafData.ofIdealTop (Ideal.span {h})) (ζ : (centre X I).left)
    (hζ : closure {ζ} ∈ irreducibleComponents (centre X I).left)
    (D : (overRestrict X I.support.compl).left.Opens)
    (hD : Dense (D : Set (overRestrict X I.support.compl).left)) :
    ∃ (V : X.left.Opens)
      (ζV : (centre (overRestrict X V) (I.comap (overRestrictι X V).left)).left)
      (w : overRestrict (overRestrict X V) (I.comap (overRestrictι X V).left).support.compl ⟶
        overRestrict X I.support.compl),
      (centreMap (overRestrictι X V) I).left ζV = ζ ∧
      IsPullback w
        (overRestrictι (overRestrict X V) (I.comap (overRestrictι X V).left).support.compl)
        (overRestrictι X I.support.compl) (overRestrictι X V) ∧
      Set.range w.left.base ⊆ Set.range D.ι.base := by
  have hV := exists_opens_inter_subset_image hX hh hI ζ hζ D hD
  obtain ⟨V, hζV, hVD⟩ := hV
  have hζ' : ζ ∈ Set.range (centreMap (overRestrictι X V) I).left := by
    rw [range_centreMap, Set.mem_preimage, range_overRestrictι]
    exact hζV
  obtain ⟨ζV, rfl⟩ := hζ'
  have hsq := exists_isPullback_overRestrictι_comap I V
  obtain ⟨w, sq⟩ := hsq
  have hw : Set.range w.left.base ⊆ Set.range D.ι.base := by
    rintro _ ⟨x, rfl⟩
    have hx := congrArg (fun f ↦ f.left.base x) sq.w
    simp only [Over.comp_left, Scheme.Hom.comp_base, TopCat.hom_comp,
      ContinuousMap.comp_apply] at hx
    have hmem : (overRestrictι X I.support.compl).left.base (w.left.base x) ∈
        (V : Set X.left) ∩ (I.support.compl : Set X.left) := by
      refine ⟨?_, ?_⟩
      · rw [hx, ← range_overRestrictι X V]
        exact ⟨_, rfl⟩
      · rw [← range_overRestrictι X I.support.compl]
        exact ⟨_, rfl⟩
    have hd := hVD hmem
    obtain ⟨d, hd, hdx⟩ := hd
    rw [Scheme.Opens.range_ι,
      ← (overRestrictι X I.support.compl).left.isOpenEmbedding.injective hdx]
    exact hd
  exact ⟨V, ζV, w, rfl, sq, hw⟩

end Geometry

open PadicAlgCl

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (k' : Type u) [Field k'] [Algebra k k']
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- **Reduction of the generic vanishing along a divisor to the lisse case** (the shrinking step
of blueprint `lemma-vanishing-generic-points-principal-divisor--1`): let `X` be normal, `Z = V(h)`,
`j : X ∖ Z ⟶ X`, `ζ` a generic point of `Z` and `F` a bounded constructible complex of `𝔽_E`-module
objects on `X ∖ Z`. There is an open neighbourhood `V` of `ζ` in `X`, with `Z ∩ V = V(h|_V)` and `ζ`
corresponding to a generic point `ζ_V` of `Z ∩ V`, such that the restriction `K` of `F` to `V ∖ Z`
comes from a bounded étale complex `F'` with finite locally constant homology sheaves, and the
vanishing of `Le^* Ψ_V(j_{V!} K)` near `ζ_V` implies that of `Le^* Ψ_X(j_! F)` near `ζ`. -/
theorem exists_opens_lisse_reduction (hX : IsNormalScheme X.left) {h : Γ(X.left, ⊤)}
    (hh : h ≠ 0) {I : X.left.IdealSheafData}
    (hI : I = IdealSheafData.ofIdealTop (Ideal.span {h}))
    (ζ : (centre X I).left) (hζ : closure {ζ} ∈ irreducibleComponents (centre X I).left)
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (F : DerivedCategory (Mod (Sheaf (ProEt.topology (overRestrict X I.support.compl).left)
      Ab.{u + 1}) (condensedRingObj (Profinite.continuousMapRingObj (integersResidueField ℓ E.1))
        (overRestrict X I.support.compl).left)))
    (hF : boundedConstructible _ F) :
    ∃ (V : X.left.Opens)
      (ζV : (centre (overRestrict X V) (I.comap (overRestrictι X V).left)).left),
      (centreMap (overRestrictι X V) I).left ζV = ζ ∧
      IsNormalScheme (overRestrict X V).left ∧
      (overRestrictι X V).left.appTop h ≠ 0 ∧
      I.comap (overRestrictι X V).left =
        IdealSheafData.ofIdealTop (Ideal.span {(overRestrictι X V).left.appTop h}) ∧
      closure {ζV} ∈
        irreducibleComponents (centre (overRestrict X V) (I.comap (overRestrictι X V).left)).left ∧
      ∃ (K : DerivedCategory (Mod (Sheaf (ProEt.topology (overRestrict (overRestrict X V)
          (I.comap (overRestrictι X V).left).support.compl).left) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj (integersResidueField ℓ E.1))
            (overRestrict (overRestrict X V)
              (I.comap (overRestrictι X V).left).support.compl).left)))
        (F' : DerivedCategory (Sheaf (overRestrict (overRestrict X V)
          (I.comap (overRestrictι X V).left).support.compl).left.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} (integersResidueField ℓ E.1))))),
        boundedConstructible _ K ∧
        (∃ a b : ℤ, F'.IsGE a ∧ F'.IsLE b) ∧
        (∀ n : ℤ, IsFiniteLocallyConstantSheaf ((DerivedCategory.homologyFunctor _ n).obj F')) ∧
        Nonempty ((finiteCoefficientDerivedEquivalence _ (integersResidueField ℓ E.1)).functor.obj
            K ≅ D(ν^*(_)[ModuleCat.{u + 1} (ULift.{u + 1} (integersResidueField ℓ E.1))]).obj F') ∧
        (nearbyCyclesVanishNear (overRestrict X V) (I.comap (overRestrictι X V).left) k'
            (Profinite.continuousMapRingObj (integersResidueField ℓ E.1)) ζV
            (D(((overRestrictι (overRestrict X V)
              (I.comap (overRestrictι X V).left).support.compl).left)_!open⟦
                Profinite.continuousMapRingObj (integersResidueField ℓ E.1)⟧).obj K) →
          nearbyCyclesVanishNear X I k'
            (Profinite.continuousMapRingObj (integersResidueField ℓ E.1)) ζ
            (D(((overRestrictι X I.support.compl).left)_!open⟦
              Profinite.continuousMapRingObj (integersResidueField ℓ E.1)⟧).obj F)) := by
  have := hX.1
  -- the étale model of `F` and a stratification on which its homology is lisse
  refine ((DerivedCategory.boundedConstructible_iff _ _ _).1
    (isEtaleOrigin_of_isConstructible _ hF)).elim fun F₀ hmodel ↦ ?_
  have hF₀ := hmodel.1
  refine hmodel.2.elim fun e₀ ↦ ?_
  have key := exists_stratification_isFiniteLocallyConstantSheaf_upperStar_homology
    (A := ModuleCat.{u + 1} (ULift.{u + 1} (integersResidueField ℓ E.1))) F₀
    (by exact_mod_proofs hF₀)
  refine key.elim fun R hR ↦ ?_
  refine (exists_opens_pullback_range_subset hX hh hI ζ hζ
    R.interiorUnion R.dense_interiorUnion).elim fun V hV ↦ ?_
  refine hV.elim fun ζV hζV ↦ ?_
  refine hζV.elim fun w hw ↦ ?_
  have hζeq := hw.1
  have sq := hw.2.1
  have hw := hw.2.2
  have : Nonempty (overRestrict X V).left :=
    ⟨(centreι (overRestrict X V) (I.comap (overRestrictι X V).left)).left ζV⟩
  let K := (boundedConstructibleUpperStar
    (Profinite.continuousMapRingObj (integersResidueField ℓ E.1)) ℓ w).obj ⟨F, hF⟩
  refine ⟨V, ζV, hζeq, hX.of_isOpenImmersion (overRestrictι X V).left,
    (overRestrictι X V).left.appTop_ne_zero_of_isOpenImmersion hh, ?_,
    closure_singleton_mem_irreducibleComponents_of_centreMap (overRestrictι X V) I hζeq hζ,
    K.obj,
    D(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (integersResidueField ℓ E.1)))
      w.left).obj F₀,
    K.property, ?_, fun n ↦ ?_,
    ⟨finiteCoefficientDerivedEquivalenceLeftDerivedUpperStarIso _ w.left e₀.symm⟩, fun hK ↦ ?_⟩
  · rw [hI, IdealSheafData.comap_ofIdealTop, Ideal.map_span, Set.image_singleton]
  · obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ :=
      (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (integersResidueField ℓ E.1)))
        w.left).bounded_mapDerivedCategory_obj hF₀.1
    exact ⟨a, b, ha, hb⟩
  · exact R.isFiniteLocallyConstantSheaf_homology_mapDerivedCategory_upperStar
      w.left hw F₀ n (hR n)
  · rw [← hζeq]
    exact nearbyCyclesVanishNear_of_isOpenImmersion (overRestrictι X V) I k' _ _ ζV
      ((nearbyCyclesVanishNear _ _ k' _ ζV).prop_of_iso
        ((boundedConstructible _).ι.mapIso
          ((boundedConstructibleOpenImmersionLowerShriekBaseChangeIso' _ ℓ sq).app
            ⟨F, hF⟩)).symm hK)


end AlgebraicGeometry.ProEtale.CondensedRing
