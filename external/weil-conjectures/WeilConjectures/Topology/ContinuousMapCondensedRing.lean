/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap
public import WeilConjectures.CategoryTheory.SheafTensor

/-!
# Continuous-map condensed rings with arbitrary coefficient universe

Source: blueprint `sec-proetale-coefficients/sk-def-sfb-condensed-ring/`
`def-sfb-continuous-map-condensed-ring.md`
(blueprint: proposition-pro-etale-site-separably-closed--3).

The upstream continuous-map construction fixes the coefficient ring in `Type 0`.
These universe-polymorphic versions retain the same sections, restrictions and canonical
ring-object construction, allowing independent universes for the profinite sets and ring.
The common coefficient universe is `max u v + 1`, so sheafification is available.
-/

@[expose] public section

universe u v

open CategoryTheory Opposite
open scoped CategoryTheory.MonoidalClosed

namespace Profinite

/-- Continuous maps into an arbitrary topological ring, with pointwise operations and
precomposition restrictions. The lift changes only the universe of sections.
Source: blueprint `def-sfb-continuous-map-condensed-ring.md`, displayed formula
(blueprint: proposition-pro-etale-site-separably-closed--3). -/
noncomputable def continuousMapRingPresheafOfUniverse (T : Type v) [TopologicalSpace T]
    [Ring T] [IsTopologicalRing T] : Profinite.{u}ᵒᵖ ⥤ RingCat.{max u v + 1} where
  obj S := RingCat.of (ULift.{max u v + 1} C(S.unop, T))
  map f := RingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      (((ContinuousMap.compRightAlgHom ℤ T f.unop.hom.hom).toRingHom).comp
        ULift.ringEquiv.toRingHom))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The continuous-map presheaf is a sheaf of unital rings.
Source: blueprint `def-sfb-continuous-map-condensed-ring.proof.md`, conditions (a),(b)
(blueprint: proposition-pro-etale-site-separably-closed--3).

Proof: identify the underlying type-valued presheaf with the universe lift of
`ContinuousMap.yonedaPresheaf`. Universe lifting preserves sheafness. Apply
`lem-sfb-profinite-coherent-sheaf-criterion` to this presheaf: finite coproducts give
products, including the empty coproduct. For an effective epimorphism of profinite sets,
`Profinite.effectiveEpi_tfae` gives surjectivity, and
`lem-sfb-compact-hausdorff-surjection-quotient` makes it a quotient map. The existing
`equalizerCondition_yonedaPresheaf` descends compatible functions along that quotient.
Finally the forgetful functor from rings to types reflects finite limits, so
`Presheaf.isSheaf_coherent_of_hasPullbacks_of_comp` gives the ring-valued sheaf condition. -/
theorem isSheaf_continuousMapRingPresheafOfUniverse (T : Type v) [TopologicalSpace T]
    [Ring T] [IsTopologicalRing T] :
    Presheaf.IsSheaf (coherentTopology Profinite.{u})
      (continuousMapRingPresheafOfUniverse.{u, v} T) := by
  let e : continuousMapRingPresheafOfUniverse.{u, v} T ⋙
      forget RingCat.{max u v + 1} ≅
      ContinuousMap.yonedaPresheaf Profinite.toTopCat.{u} T ⋙
        uliftFunctor.{max u v + 1} :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)
  have h : Presheaf.IsSheaf (coherentTopology Profinite.{u})
      (continuousMapRingPresheafOfUniverse.{u, v} T ⋙
        forget RingCat.{max u v + 1}) := by
    rw [Presheaf.isSheaf_of_iso_iff e,
      isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_comp_uliftFunctor_iff,
      ← isSheaf_iff_isSheaf_of_type]
    rw [Presheaf.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition]
    refine ⟨inferInstance, ?_⟩
    apply +allowSynthFailures equalizerCondition_yonedaPresheaf Profinite.toTopCat.{u} T
    intro Z B π hπ
    exact .of_surjective_continuous (((Profinite.effectiveEpi_tfae π).out 1 3).mp hπ)
      π.hom.hom.continuous
  exact Presheaf.isSheaf_coherent_of_hasPullbacks_of_comp
    (continuousMapRingPresheafOfUniverse.{u, v} T)
    (forget RingCat.{max u v + 1}) h

/-- The condensed ring with sections C(S,T) and precomposition restrictions.
Source: blueprint `def-sfb-continuous-map-condensed-ring.md`, sheaf assertion
(blueprint: proposition-pro-etale-site-separably-closed--3). -/
noncomputable def continuousMapRingSheafOfUniverse (T : Type v) [TopologicalSpace T]
    [Ring T] [IsTopologicalRing T] :
    Sheaf (coherentTopology Profinite.{u}) RingCat.{max u v + 1} :=
  ⟨continuousMapRingPresheafOfUniverse T,
    isSheaf_continuousMapRingPresheafOfUniverse T⟩

/-- The actual abelian sheaf underlying the continuous-map condensed ring.
Source: blueprint `def-sfb-continuous-map-condensed-ring.md`, last sentence
(blueprint: proposition-pro-etale-site-separably-closed--3). -/
noncomputable def continuousMapRingObjOfUniverse (T : Type v) [TopologicalSpace T]
    [Ring T] [IsTopologicalRing T] :
    Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{max u v + 1} :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{max u v + 1} AddCommGrpCat.{max u v + 1})).obj
      (continuousMapRingSheafOfUniverse T)

/-- The canonical ring-object structure, obtained by the ring-sheaf construction of
`sk-def-sfb-ring-object`, for the sheafified tensor over the integers. This transports the
sectionwise multiplication and integer unit along the sheafification counit.
Source: blueprint `def-sfb-continuous-map-condensed-ring.md`, last sentence
(blueprint: proposition-pro-etale-site-separably-closed--3). -/
@[instance_reducible]
noncomputable def continuousMapRingObjOfUniverseMonObj (T : Type v) [TopologicalSpace T]
    [Ring T] [IsTopologicalRing T] :
    @MonObj (Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{max u v + 1}) _
      (sfbSheafTensorStructure (A := AddCommGrpCat.{max u v + 1})
        (coherentTopology Profinite.{u})).monoidal
      (continuousMapRingObjOfUniverse T) := by
  let h := presheaf_enrichedHoms_exist
    (C := Profinite.{u}) (A := AddCommGrpCat.{max u v + 1})
  letI : ∀ (F G : Profinite.{u}ᵒᵖ ⥤ AddCommGrpCat.{max u v + 1}),
    Enriched.FunctorCategory.HasEnrichedHom AddCommGrpCat.{max u v + 1} F G := h.1
  letI : ∀ (F G : Profinite.{u}ᵒᵖ ⥤ AddCommGrpCat.{max u v + 1}),
    Enriched.FunctorCategory.HasFunctorEnrichedHom AddCommGrpCat.{max u v + 1} F G := h.2
  exact Sheaf.monObj_sheafCompose_obj (coherentTopology Profinite.{u})
    (continuousMapRingSheafOfUniverse T)

end Profinite

namespace Profinite

section

open CategoryTheory Opposite
open scoped CategoryTheory.MonoidalClosed

/-- The canonical ring object is commutative when the topological ring is commutative.
Source: blueprint `def-sfb-continuous-map-condensed-ring.md`, final clause
(blueprint: proposition-pro-etale-site-separably-closed--3).

Proof: for sections a,b, evaluation at every point gives a(s)b(s)=b(s)a(s).
Their lifted section rings are therefore commutative. Apply the commutative case of
`sk-def-sfb-ring-object`, specifically `Sheaf.isCommMonObj_sheafCompose_obj`, to the
continuous-map sheaf. Its counit-transport construction is exactly the monoid structure
`continuousMapRingObjOfUniverseMonObj`; the tensor and braiding are the canonical
sheafified tensor over the integers supplied by `sk-def-sfb-sheaf-tensor`. -/
theorem isCommMonObj_continuousMapRingObjOfUniverse (T : Type v) [TopologicalSpace T]
    [CommRing T] [IsTopologicalRing T] :
    @IsCommMonObj
      (Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{max u v + 1}) _
      (sfbSheafTensorStructure (A := AddCommGrpCat.{max u v + 1})
        (coherentTopology Profinite.{u})).monoidal
      (sfbSheafTensorStructure (A := AddCommGrpCat.{max u v + 1})
        (coherentTopology Profinite.{u})).symmetric.toBraidedCategory
      (continuousMapRingObjOfUniverse T) (continuousMapRingObjOfUniverseMonObj T) := by
  let h := presheaf_enrichedHoms_exist
    (C := Profinite.{u}) (A := AddCommGrpCat.{max u v + 1})
  let : ∀ (F G : Profinite.{u}ᵒᵖ ⥤ AddCommGrpCat.{max u v + 1}),
    Enriched.FunctorCategory.HasEnrichedHom AddCommGrpCat.{max u v + 1} F G := h.1
  let : ∀ (F G : Profinite.{u}ᵒᵖ ⥤ AddCommGrpCat.{max u v + 1}),
    Enriched.FunctorCategory.HasFunctorEnrichedHom AddCommGrpCat.{max u v + 1} F G := h.2
  exact Sheaf.isCommMonObj_sheafCompose_obj (coherentTopology Profinite.{u})
    (continuousMapRingSheafOfUniverse T)
    fun S (a b : ULift.{max u v + 1} C(S.unop, T)) ↦ mul_comm a b

end

end Profinite
