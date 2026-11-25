/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.ComponentClassReduction
public import WeilConjectures.TraceFormula.Specialization.DeformationSupport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosedComplement

/-!

# The specialization of the fixed locus inverts the counit of a component

Let `j : B ⟶ F` be an open subscheme of the fixed locus containing the point above `y`, and
`e : j_! ℚ̄_ℓ ⟶ ℚ̄_ℓ` the adjoint of `ℚ̄_ℓ ≅ j^! ℚ̄_ℓ`
(`ProEtale.CondensedRing.Correspondence.IsContractingAt.componentCounit`). For the deformation
trace specialization, `Ψ_F(e)` is an isomorphism
(`ProEtale.CondensedRing.Correspondence.IsContractingAt.isIso_ΨF_map_componentCounit`, fact (I)
of `ComponentClassReduction`), whatever the exchanges `ν_c`, `ν_X`:

* `Ψ_F = Lι'^* Ψ_C Rι_*` is triangulated, the specialization `Ψ_C` being induced by the
  triangulated nearby cycles `Li^* Rj_* Lε^*`;
* `Lj^* e` is invertible, since the unit of `Rj_! ⊣ Rj^!` is (`Rj_! ≅ j_!` is fully faithful)
  and `Rj^! ≅ Lj^*` (`ProEtale.CondensedRing.isIso_upperStar_map_homEquiv_symm`);
* so the cone `W` of `e` restricts to zero on `B`, hence `W ≅ Ri₀_* Li₀^* W` for the closed
  complement `i₀ : F ∖ B ⟶ F`, and `Ψ_C` kills `R(ι i₀)_* N` because `ι i₀` avoids `y`
  (`ProEtale.CondensedRing.isIso_map_of_isIso_upperStar_map`,
  `ProEtale.CondensedRing.isZero_specialization_obj_lowerStar_obj`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section Specialization

variable {k' : Type u} [Field k'] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] [Algebra k k'] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The specialization commutes with the shifts (as the nearby cycles do). -/
noncomputable instance commShift_specialization (x : RationalPoint X) :
    (specialization (ℓ := ℓ) k' x).CommShift ℤ := by
  delta specialization NearbyCyclesModel.boundedConstructibleNearbyCycles
    NearbyCyclesModel.nearbyCycles
  infer_instance

instance isTriangulated_specialization (x : RationalPoint X) :
    (specialization (ℓ := ℓ) k' x).IsTriangulated := by
  delta specialization NearbyCyclesModel.boundedConstructibleNearbyCycles
    NearbyCyclesModel.nearbyCycles
  infer_instance

end Specialization

section Generic

variable {F U Z : Over (Spec (.of k))} [LocallyOfFiniteType F.hom] [QuasiCompact F.hom]
  [IsSeparated F.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

include ℓ in
/-- A morphism `e` of `Dᵇc(F)` whose restriction to an open `U` is invertible is inverted by any
triangulated functor `G` killing the complexes `Ri_* N` supported on the closed complement `Z`:
the cone `W` of `e` restricts to zero on `U`, so `W ≅ Ri_* Li^* W` and `G(W) = 0`. -/
theorem isIso_map_of_isIso_upperStar_map {D : Type*} [Category D] [Preadditive D]
    [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (G : Dᵇc(F.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ D) [G.CommShift ℤ] [G.IsTriangulated]
    (j : U ⟶ F) [IsOpenImmersion j.left] [QuasiCompact j.left] (i : Z ⟶ F)
    [IsClosedImmersion i.left] (hij : IsCompl (Set.range i.left.base) (Set.range j.left.base))
    (hG : ∀ N, IsZero (G.obj ((boundedConstructibleLowerStar ℓ i).obj N)))
    {P Q : Dᵇc(F.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (e : P ⟶ Q)
    (he : IsIso ((boundedConstructibleUpperStar _ ℓ j).map e)) : IsIso (G.map e) := by
  obtain ⟨W, g, h, hT⟩ := distinguished_cocone_triangle e
  have hW : IsZero ((boundedConstructibleUpperStar _ ℓ j).obj W) :=
    (Triangle.isZero₃_iff_isIso₁ _
      ((boundedConstructibleUpperStar _ ℓ j).map_distinguished _ hT)).2 he
  set adj := boundedConstructibleUpperStarLowerStarAdjunction ℓ i
  have hu : IsIso (adj.unit.app W) := by
    refine isIso_of_isIso_boundedConstructibleUpperStar_map_of_isCompl _ ℓ i j hij _ ?_ ?_
    · exact isIso_of_source_target_iso_zero _ hW.isoZero
        (isZero_boundedConstructibleUpperStar_obj_lowerStar_obj ℓ j i hij.symm.disjoint
          _).isoZero
    · have := adj.left_triangle_components W
      have : IsIso ((boundedConstructibleUpperStar _ ℓ i).map (adj.unit.app W) ≫
          adj.counit.app _) := by rw [this]; exact IsIso.id _
      exact IsIso.of_isIso_comp_right _ (adj.counit.app _)
  exact (Triangle.isZero₃_iff_isIso₁ _ (G.map_distinguished _ hT)).1
    ((hG _).of_iso (G.mapIso (asIso (adj.unit.app W))))

end Generic

section OpenImmersion

variable {U F : Over (Spec (.of k))} [LocallyOfFiniteType F.hom] [QuasiCompact F.hom]
  [IsSeparated F.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  (j : U ⟶ F) [IsOpenImmersion j.left]

include ℓ in
/-- Along an open immersion `j`, the pullback `Lj^*` inverts the adjoint `j_! M ⟶ N` of an
isomorphism `M ≅ Rj^! N`: the unit of `Rj_! ⊣ Rj^!` is invertible (`Rj_! ≅ j_!` is fully
faithful) and `Rj^! ≅ Lj^*`. -/
theorem isIso_upperStar_map_homEquiv_symm {M : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    {N : Dᵇc(F.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (φ : M ⟶ (boundedConstructibleUpperShriek ℓ j).obj N)
    [IsIso φ] : IsIso ((boundedConstructibleUpperStar _ ℓ j).map
      (((boundedConstructibleUpperShriekAdjunction ℓ j).homEquiv _ _).symm φ)) := by
  set adj := boundedConstructibleUpperShriekAdjunction ℓ j
  have hff := (fullyFaithfulBoundedConstructibleOpenImmersionLowerShriek _ ℓ j).ofIso
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).symm
  have := hff.full
  have := hff.faithful
  have hφ : adj.unit.app M ≫
      (boundedConstructibleUpperShriek ℓ j).map ((adj.homEquiv _ _).symm φ) = φ := by
    have h := adj.homEquiv_unit M N ((adj.homEquiv _ _).symm φ)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  have : IsIso ((boundedConstructibleUpperShriek ℓ j).map ((adj.homEquiv _ _).symm φ)) := by
    have : IsIso (adj.unit.app M ≫
        (boundedConstructibleUpperShriek ℓ j).map ((adj.homEquiv _ _).symm φ)) := by
      rw [hφ]; infer_instance
    exact IsIso.of_isIso_comp_left (adj.unit.app M) _
  exact (NatIso.isIso_map_iff (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ j)
    _).1 this

end OpenImmersion

section Vanishing

variable {k' : Type u} [Field k'] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] [Algebra k k']
  {C F Z : Over (Spec (.of k))} [LocallyOfFiniteType C.hom] [QuasiCompact C.hom]
  [IsSeparated C.hom] [LocallyOfFiniteType F.hom] [QuasiCompact F.hom] [IsSeparated F.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  {F' : Over (Spec (.of k'))} [LocallyOfFiniteType F'.hom] [QuasiCompact F'.hom]
  [IsSeparated F'.hom]
variable (k') in
/-- `Lι'^* Sp_{C,y} Rι_* Ri_* N = 0` when the image of the closed immersions `ι ∘ i` avoids
the rational point `y` (`isZero_specialization_obj_lowerStar_obj`). -/
lemma isZero_upperStar_specialization_lowerStar_lowerStar (y : RationalPoint C) (ι : F ⟶ C)
    [IsClosedImmersion ι.left] (i : Z ⟶ F) [IsClosedImmersion i.left]
    (ι' : F' ⟶ deformationSpecialFibre C y.left.ker k')
    (hd : Disjoint (Set.range (i ≫ ι).left.base) (Set.range y.left.base))
    (N : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsZero ((boundedConstructibleUpperStar _ ℓ ι').obj ((specialization (ℓ := ℓ) k' y).obj
      ((boundedConstructibleLowerStar ℓ ι).obj ((boundedConstructibleLowerStar ℓ i).obj
        N)))) := by
  have : IsClosedImmersion (i ≫ ι).left := by rw [Over.comp_left]; infer_instance
  exact Functor.map_isZero _ ((isZero_specialization_obj_lowerStar_obj k' y _ hd N).of_iso
    ((specialization k' y).mapIso ((boundedConstructibleLowerStarComp ℓ i ι).app N)))

end Vanishing

namespace Correspondence.IsContractingAt

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {c : Correspondence ℓ K}
  {y : RationalPoint c.C} (hc : c.IsContractingAt y) (k' : Type u) [Field k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] [Algebra k k']
  (νc : hc.SupportCompactSupportExchange (ℓ := ℓ) k')
  (νX : PointCompactSupportExchange (ℓ := ℓ) X k' (y ≫ c.c₁)) (F : c.FixedLocus)
  {B : Over (Spec (.of k))} [QuasiCompact B.hom] [IsProper B.hom] (j : B ⟶ F.F)
  [IsOpenImmersion j.left]

/-- **`Ψ_F` inverts the counit of the component** (fact (I) of `ComponentClassReduction`): if
the point of `F` above `y` lies in the open `B`, then `Ψ_F(j_! ℚ̄_ℓ ⟶ ℚ̄_ℓ)` is an isomorphism.
Indeed `Ψ_F = Lι'^* Ψ_C Rι_*` is triangulated, the morphism restricts to an isomorphism on `B`,
and `Ψ_C` kills the complexes `R(ι i₀)_* N` for the closed complement `i₀ : F ∖ B ⟶ F`, whose
image in `C` avoids `y` (`isZero_specialization_obj_lowerStar_obj`). -/
theorem isIso_ΨF_map_componentCounit
    (hy : (F.liftPoint y hc.comp_c₁_eq_comp_c₂).left.base (default : Spec (.of k)) ∈
      Set.range j.left.base) :
    IsIso ((hc.deformationTraceSpecialization k' νc νX F).ΨF.map (componentCounit (ℓ := ℓ) j)) := by
  change IsIso ((boundedConstructibleLowerStar ℓ F.ι ⋙ specialization (ℓ := ℓ) k' y ⋙
    boundedConstructibleUpperStar _ ℓ (hc.specialFixedLocus k').ι).map _)
  refine isIso_map_of_isIso_upperStar_map _ j (overClosedComplement j)
    (isCompl_range_overClosedComplement j) (fun N ↦ ?_) _
    (isIso_upperStar_map_homEquiv_symm j _)
  have hd : Disjoint (Set.range (overClosedComplement j ≫ F.ι).left.base)
      (Set.range y.left.base) := by
    have : Subsingleton (point k).left := inferInstanceAs (Subsingleton (Spec (.of k)))
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨z, rfl⟩ ⟨p, hp⟩
    have hp' : y.left.base p = F.ι.left.base
        ((F.liftPoint y hc.comp_c₁_eq_comp_c₂).left.base (default : Spec (.of k))) := by
      rw [Subsingleton.elim p (default : Spec (.of k)), ← Scheme.Hom.comp_apply,
        ← Over.comp_left, FixedLocus.liftPoint_ι]
    rw [Over.comp_left, Scheme.Hom.comp_apply, hp'] at hp
    obtain ⟨b, hb⟩ := hy
    exact Set.disjoint_left.mp (isCompl_range_overClosedComplement j).disjoint ⟨z, rfl⟩
      ⟨b, hb.trans (F.ι.left.isClosedEmbedding.injective hp)⟩
  exact isZero_upperStar_specialization_lowerStar_lowerStar k' y F.ι _ _ hd N

end Correspondence.IsContractingAt

end AlgebraicGeometry.ProEtale.CondensedRing
