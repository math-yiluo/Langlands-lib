/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitSliceInvariantsAverage
public import WeilConjectures.TraceFormula.Specialization.TraitSliceInvariantsDegree
public import WeilConjectures.TraceFormula.Specialization.TraitSliceInvariantsIntegralModel

/-!

# The slicing exchange as the inclusion of the invariants, granted the cartesian step

Let `M''` be the base change of a model `M` of finite type over `S = Spec k'⟦t⟧` along
`v : Spec K⟦t⟧ ⟶ Y`, `K` algebraically closed, and `φ : M'' ⟶ M` the projection. It factors as
`M'' ⟶ N''_{L^sep} ⟶ N'' ⟶ M` through the Galois layer of the change-of-traits model `N''`
(`NearbyCyclesModel.baseChangeGaloisModel`), the last arrow `χ` being its cartesian part. Granted
that the pullback exchange of `χ` is invertible ("M1 at `T`", an explicit hypothesis), the
slicing exchange `α_φ` is the inclusion of the invariants of the generic automorphisms
(`NearbyCyclesModel.exists_subgroup_pullbackExchange_baseChangeHom_of_isIso_cartesian`): a
subgroup `V` of finite index acts trivially and `α_φ` is split by the average over `P' ⧸ V`.

The proof applies the stabilization of nearby cycles along Galois layers to `N''`
(`NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom_of_integralModel`, with the
integral model of `NearbyCyclesModel.exists_integralModel_baseChangeGaloisModel` and the degrees of
`AlgebraicGeometry.not_dvd_finrank_traitTensorCompositum`), transports the average along
`M'' ⟶ N''_{L^sep}` and `χ`
(`NearbyCyclesModel.exists_retraction_pullbackExchange_of_comp_galoisLayer`), and reindexes it by
`P' ⧸ V ≃ Gal(L₁ / L)` (`MonoidHom.card_nsmul_eq_sum_quotient_ker'`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme PadicAlgCl

attribute [local instance] traitGenericFieldAlgebra

/-- Constructibility of a derived pullback passes to any further factorization. -/
private lemma boundedConstructible_leftDerivedUpperStar_obj_of_factorization
    {Z Y X : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X) (fg : Z ⟶ X) (hfg : f ≫ g = fg)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (hA : boundedConstructible (condensedRingObj Λ Y) (L((g)^*⟦Λ⟧).obj A)) :
    boundedConstructible (condensedRingObj Λ Z) (L((fg)^*⟦Λ⟧).obj A) :=
  (boundedConstructible _).prop_of_iso ((leftDerivedUpperStarCompOfEq Λ hfg).app A).symm
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ f _ hA)

/-- An invertible exchange transports triviality of the intertwined automorphism action. -/
private lemma autAction_eq_id_of_pullbackExchange_intertwines
    {X S : Scheme.{u}} {M N : NearbyCyclesModel X S}
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (ρ : M.Hom N (𝟙 X) (𝟙 S)) (σ : M.Hom M (𝟙 X) (𝟙 S))
    (τ : N.Hom N (𝟙 X) (𝟙 S))
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) (hρ : IsIso ((ρ.pullbackExchange Λ).app A))
    (hint : (ρ.pullbackExchange Λ).app A ≫ σ.autAction Λ (L((𝟙 X)^*⟦Λ⟧).obj A) =
      L((𝟙 S)^*⟦Λ⟧).map (τ.autAction Λ A) ≫ (ρ.pullbackExchange Λ).app A)
    (hτ : τ.autAction Λ (L((𝟙 X)^*⟦Λ⟧).obj A) = 𝟙 _) :
    σ.autAction Λ (L((𝟙 X)^*⟦Λ⟧).obj A) = 𝟙 _ := by
  have hτ' : τ.autAction Λ A = 𝟙 _ :=
    eq_id_of_naturality_of_iso _ (fun f ↦ Hom.autAction_naturality Λ τ f)
      ((leftDerivedUpperStarId Λ X).app A).symm hτ
  rw [hτ', CategoryTheory.Functor.map_id, Category.id_comp] at hint
  exact (cancel_epi _).1 (hint.trans (Category.comp_id _).symm)

/-- Restriction through a Galois equivalence has the expected kernel and lifted section. -/
private lemma exists_surjective_galoisRestriction_of_equiv
    {G L Ω : Type*} [Group G] [Field L] [Field Ω] [Algebra L Ω] [IsGalois L Ω]
    (eG : G ≃* Gal(Ω/L)) (L₁ : FiniteGaloisIntermediateField L Ω) :
    ∃ π : G →* Gal(L₁.toIntermediateField/L), Function.Surjective π ∧
      (∀ σ ∈ π.ker, eG σ ∈ L₁.toIntermediateField.fixingSubgroup) ∧
      ∀ τ : Gal(L₁.toIntermediateField/L), π (eG.symm (τ.liftNormal Ω)) = τ := by
  let π := (AlgEquiv.restrictNormalHom (F := L) (K₁ := Ω) L₁.toIntermediateField).comp
    eG.toMonoidHom
  refine ⟨π, (AlgEquiv.restrictNormalHom_surjective Ω).comp eG.surjective, ?_, ?_⟩
  · intro σ hσ
    rw [← IntermediateField.restrictNormalHom_ker]
    exact hσ
  · intro τ
    simp only [π, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    exact τ.restrict_liftNormal Ω

/-- Exchange invertibility is independent of the presentation of its source model. -/
private lemma isIso_pullbackExchange_app_of_model_eq
    {X S S' : Scheme.{u}} {M₀ M₁ : NearbyCyclesModel X S} {N : NearbyCyclesModel X S'}
    {f : X ⟶ X} {f' : S ⟶ S'}
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (φ₀ : M₀.Hom N f f') (φ₁ : M₁.Hom N f f')
    (hM : M₀ = M₁) (hφ : HEq φ₀ φ₁)
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (h : IsIso ((φ₀.pullbackExchange Λ).app A)) :
    IsIso ((φ₁.pullbackExchange Λ).app A) := by
  cases hM
  cases hφ
  exact h

/-- A Galois average is independent of the presentation of its source model. -/
private lemma galois_average_of_model_eq
    {X S : Scheme.{u}} {M₀ M₁ N : NearbyCyclesModel X S}
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {L Ω : Type*} [Field L] [Field Ω] [Algebra L Ω] [IsGalois L Ω]
    (L₁ : FiniteGaloisIntermediateField L Ω)
    (ψ₀ : M₀.Hom N (𝟙 X) (𝟙 S)) (ψ₁ : M₁.Hom N (𝟙 X) (𝟙 S))
    (act₀ : Gal(Ω/L) → M₀.Hom M₀ (𝟙 X) (𝟙 S))
    (act₁ : Gal(Ω/L) → M₁.Hom M₁ (𝟙 X) (𝟙 S))
    (hM : M₀ = M₁) (hψ : HEq ψ₀ ψ₁) (hact : HEq act₀ act₁)
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (h : ∃ r, (ψ₀.pullbackExchange Λ).app A ≫ r = 𝟙 _ ∧
      Fintype.card Gal(L₁.toIntermediateField/L) • (r ≫ (ψ₀.pullbackExchange Λ).app A) =
        ∑ τ : Gal(L₁.toIntermediateField/L),
          (act₀ (τ.liftNormal Ω)).autAction Λ (L((𝟙 X)^*⟦Λ⟧).obj A)) :
    ∃ r, (ψ₁.pullbackExchange Λ).app A ≫ r = 𝟙 _ ∧
      Fintype.card Gal(L₁.toIntermediateField/L) • (r ≫ (ψ₁.pullbackExchange Λ).app A) =
        ∑ τ : Gal(L₁.toIntermediateField/L),
          (act₁ (τ.liftNormal Ω)).autAction Λ (L((𝟙 X)^*⟦Λ⟧).obj A) := by
  cases hM
  cases hψ
  cases hact
  exact h

/-- An equivariant Galois average gives a retraction averaged over a finite quotient. -/
private lemma exists_subgroup_pullbackExchange_of_galois_average
    {X S S' : Scheme.{u}} {M'' N₁ N : NearbyCyclesModel X S}
    {M : NearbyCyclesModel X S'} {f' : S ⟶ S'}
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (ρ : M''.Hom N₁ (𝟙 X) (𝟙 S)) (ψ : N₁.Hom N (𝟙 X) (𝟙 S))
    {χ : N.Hom M (𝟙 X ≫ 𝟙 X) (𝟙 S ≫ f')} (φ : M''.Hom M (𝟙 X) f')
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (hχ : IsIso ((χ.pullbackExchange Λ).app A))
    (htot : (ρ.total ≫ ψ.total) ≫ χ.total = φ.total)
    (hgen : (ρ.generic ≫ ψ.generic) ≫ χ.generic = φ.generic)
    (hρ : ∀ C, IsIso ((ρ.pullbackExchange Λ).app C))
    {G L Ω : Type*} [Group G] [Field L] [Field Ω] [Algebra L Ω] [IsGalois L Ω]
    (eG : G ≃* Gal(Ω/L)) (L₁ : FiniteGaloisIntermediateField L Ω)
    (act : G → M''.Hom M'' (𝟙 X) (𝟙 S))
    (actΩ : Gal(Ω/L) → N₁.Hom N₁ (𝟙 X) (𝟙 S))
    (hmul : ∀ σ τ C, (act (σ * τ)).autAction Λ C =
      (act τ).autAction Λ C ≫ (act σ).autAction Λ C)
    (hint : ∀ τ D, (ρ.pullbackExchange Λ).app D ≫
        (act (eG.symm τ)).autAction Λ (L((𝟙 X)^*⟦Λ⟧).obj D) =
      L((𝟙 S)^*⟦Λ⟧).map ((actΩ τ).autAction Λ D) ≫ (ρ.pullbackExchange Λ).app D)
    (htriv : ∀ τ ∈ L₁.toIntermediateField.fixingSubgroup,
      (actΩ τ).autAction Λ (L((𝟙 X)^*⟦Λ⟧).obj A) = 𝟙 _)
    (hSA : ∃ r, (ψ.pullbackExchange Λ).app A ≫ r = 𝟙 _ ∧
      Fintype.card Gal(L₁.toIntermediateField/L) • (r ≫ (ψ.pullbackExchange Λ).app A) =
        ∑ τ : Gal(L₁.toIntermediateField/L),
          (actΩ (τ.liftNormal Ω)).autAction Λ (L((𝟙 X)^*⟦Λ⟧).obj A)) :
    ∃ (V : Subgroup G) (_ : Fintype (G ⧸ V)),
      (∀ σ ∈ V, (act σ).autAction Λ (L((𝟙 X)^*⟦Λ⟧).obj A) = 𝟙 _) ∧
      ∃ r, (φ.pullbackExchange Λ).app A ≫ r = 𝟙 _ ∧
        Fintype.card (G ⧸ V) • (r ≫ (φ.pullbackExchange Λ).app A) =
          ∑ σ : G ⧸ V, (act σ.out).autAction Λ (L((𝟙 X)^*⟦Λ⟧).obj A) := by
  have htriv' (σ : G) (hσ : eG σ ∈ L₁.toIntermediateField.fixingSubgroup) :=
    autAction_eq_id_of_pullbackExchange_intertwines Λ ρ (act (eG.symm (eG σ)))
      (actΩ (eG σ)) A (hρ A) (hint (eG σ) A) (htriv _ hσ)
  simp only [MulEquiv.symm_apply_apply] at htriv'
  refine (exists_retraction_pullbackExchange_of_comp_galoisLayer Λ ρ ψ χ φ htot hgen A
    hρ hχ Finset.univ
    (fun τ : Gal(L₁.toIntermediateField/L) ↦ act (eG.symm (τ.liftNormal Ω)))
    (fun τ ↦ actΩ (τ.liftNormal Ω)) (Fintype.card _) hSA
    (fun τ D ↦ hint (τ.liftNormal Ω) D)).elim fun r hravg ↦ ?_
  refine (exists_surjective_galoisRestriction_of_equiv eG L₁).elim fun π hπdata ↦ ?_
  have hπ := hπdata.1
  have hker := hπdata.2.1
  let : Fintype (G ⧸ π.ker) :=
    Fintype.ofEquiv _ (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv.symm
  refine ⟨π.ker, inferInstance, fun σ hσ ↦ htriv' σ (hker σ hσ), r, hravg.1, ?_⟩
  exact MonoidHom.card_nsmul_eq_sum_quotient_ker' hravg.2 π hπ
    (fun σ ↦ (act σ).autAction Λ (L((𝟙 X)^*⟦Λ⟧).obj A))
    (fun σ w hw ↦ by rw [hmul, htriv' w (hker w hw), Category.id_comp])
    (fun τ ↦ eG.symm (τ.liftNormal Ω)) hπdata.2.2 (fun _ ↦ rfl)

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]
  {X : Scheme.{u}} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  (hM : M.IsTraitModelOver q g) {Y : Scheme.{u}} (b : M.total ⟶ Y) {p : Y ⟶ trait k'}
  (hb : b ≫ p = q) (v : trait K ⟶ Y) (hv : v ≫ p = traitMap k' K)
  {ℓ : ℕ} [Fact ℓ.Prime]

/-- The total-space component of `M'' ⟶ N''_{L^sep} ⟶ N'' ⟶ M` is that of `M'' ⟶ M`. -/
lemma baseChangeToGaloisModel_comp_total :
    ((baseChangeToGaloisLayer hM b hb v hv).total ≫
      ((baseChangeGaloisModel hM b hb v hv).galoisLayerHom
        (baseChangeGaloisResidue hM b hb v hv) (traitTensorCompositumSep (PowerSeries K)
          (traitGenericField k') (traitGenericField K))).total) ≫
      (((baseChangeHom hM b hb v hv).traitChangeModelHom (traitGenericField K)
        (baseChangeTotalStructure hM b hb v hv) q g hM.isPullback_j.w
        (baseChangeHom_total_comp hM b hb v hv)).comp
          (baseChangeHom hM b hb v hv).fromCartesian).total =
      (baseChangeHom hM b hb v hv).total := by
  simp

/-- The generic component of `M'' ⟶ N''_{L^sep} ⟶ N'' ⟶ M` is that of `M'' ⟶ M`. -/
lemma baseChangeToGaloisModel_comp_generic :
    ((baseChangeToGaloisLayer hM b hb v hv).generic ≫
      ((baseChangeGaloisModel hM b hb v hv).galoisLayerHom
        (baseChangeGaloisResidue hM b hb v hv) (traitTensorCompositumSep (PowerSeries K)
          (traitGenericField k') (traitGenericField K))).generic) ≫
      (((baseChangeHom hM b hb v hv).traitChangeModelHom (traitGenericField K)
        (baseChangeTotalStructure hM b hb v hv) q g hM.isPullback_j.w
        (baseChangeHom_total_comp hM b hb v hv)).comp
          (baseChangeHom hM b hb v hv).fromCartesian).generic =
      (baseChangeHom hM b hb v hv).generic := by
  rw [Hom.comp_generic, Category.assoc]
  exact (baseChangeToGaloisLayer_generic_fst_fst_assoc hM b hb v hv _).trans
    (pullback.lift_fst _ _ _)

/-- **The slicing exchange is the inclusion of the invariants, given the cartesian step**: if the
pullback exchange of the cartesian part `χ : N'' ⟶ M` of the base change is invertible at `A`
(`hM1`) and `Lε^* A ≅ Lj^* B` for a bounded constructible `B` on the total space, a subgroup `V` of
finite index of the generic automorphisms acts trivially on `Ψ_{M''} A`, and the pullback
exchange of `M'' ⟶ M` has a retraction `r` with `[P' : V] • (r ≫ α) = ∑_{σ ∈ P' ⧸ V} σ`. -/
theorem exists_subgroup_pullbackExchange_baseChangeHom_of_isIso_cartesian [IsSeparated p]
    [IsAlgClosed K] [Fact (ringChar k' ≠ ℓ)]
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hA : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.generic)
      (L((M.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A))
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.total) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.total))}
    (hB : boundedConstructible _ B)
    (eB : L((M.j)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj B ≅
      L((M.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A)
    (hM1 : IsIso (((((baseChangeHom hM b hb v hv).traitChangeModelHom (traitGenericField K)
        (baseChangeTotalStructure hM b hb v hv) q g hM.isPullback_j.w
        (baseChangeHom_total_comp hM b hb v hv)).comp
          (baseChangeHom hM b hb v hv).fromCartesian).pullbackExchange
            (Profinite.padicAlgClRingObj ℓ)).app A)) :
    ∃ (V : Subgroup (GenericAut k' K)) (_ : Fintype (GenericAut k' K ⧸ V)),
      (∀ σ ∈ V, (baseChangeAut hM b hb v hv σ).autAction (Profinite.padicAlgClRingObj ℓ)
          (L((𝟙 X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A) = 𝟙 _) ∧
      ∃ r, ((baseChangeHom hM b hb v hv).pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app A ≫
          r = 𝟙 _ ∧
        Fintype.card (GenericAut k' K ⧸ V) •
          (r ≫ ((baseChangeHom hM b hb v hv).pullbackExchange
            (Profinite.padicAlgClRingObj ℓ)).app A) =
        ∑ σ : GenericAut k' K ⧸ V, (baseChangeAut hM b hb v hv σ.out).autAction
          (Profinite.padicAlgClRingObj ℓ) (L((𝟙 X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A) := by
  have hT := IsTraitModelOver.baseChange hM b hb v hv
  have : LocallyOfFiniteType (baseChangeTotalStructure hM b hb v hv) := hT.locallyOfFiniteType
  have : QuasiCompact (baseChangeTotalStructure hM b hb v hv) := hT.quasiCompact
  have := hT.locallyOfFiniteType
  have := hT.quasiCompact
  have := hT.isSeparated
  have hc := (baseChangeHom hM b hb v hv).isPullback_cartesianModelTensor hM.isPullback_j
    (baseChangeHom_total_comp hM b hb v hv)
  have : LocallyOfFiniteType ((baseChangeHom hM b hb v hv).cartesianModelTensor
      (baseChangeTotalStructure hM b hb v hv) q g hM.isPullback_j.w
      (baseChangeHom_total_comp hM b hb v hv)) := MorphismProperty.of_isPullback hc.flip ‹_›
  have : QuasiCompact ((baseChangeHom hM b hb v hv).cartesianModelTensor
      (baseChangeTotalStructure hM b hb v hv) q g hM.isPullback_j.w
      (baseChangeHom_total_comp hM b hb v hv)) := MorphismProperty.of_isPullback hc.flip ‹_›
  have : LocallyOfFiniteType (baseChangeGaloisResidue hM b hb v hv) :=
    MorphismProperty.pullback_snd _ _ ‹_›
  have : QuasiCompact (baseChangeGaloisResidue hM b hb v hv) :=
    MorphismProperty.pullback_snd _ _ ‹_›
  have : IsLocallyNoetherian (baseChangeGaloisModel hM b hb v hv).generic :=
    LocallyOfFiniteType.isLocallyNoetherian (baseChangeGaloisResidue hM b hb v hv)
  have : CompactSpace (baseChangeGaloisModel hM b hb v hv).generic :=
    QuasiCompact.compactSpace_of_compactSpace (baseChangeGaloisResidue hM b hb v hv)
  have : IsNoetherian (baseChangeGaloisModel hM b hb v hv).generic := ⟨⟩
  have : QuasiCompact (baseChangeSpecial b v).hom :=
    MorphismProperty.of_isPullback hT.isPullback_i ‹_›
  have : IsSeparated (baseChangeSpecial b v).hom :=
    MorphismProperty.of_isPullback hT.isPullback_i ‹_›
  have : CompactSpace (baseChangeGaloisModel hM b hb v hv).total :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd b v)
  have : QuasiSeparatedSpace (baseChangeGaloisModel hM b hb v hv).total :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd b v)
  have : CompactSpace (baseChangeSpecial b v).left :=
    QuasiCompact.compactSpace_of_compactSpace (baseChangeSpecial b v).hom
  have : QuasiSeparatedSpace (baseChangeSpecial b v).left :=
    quasiSeparatedSpace_of_quasiSeparated (baseChangeSpecial b v).hom
  have hC := boundedConstructible_leftDerivedUpperStar_obj_of_factorization
    (Z := (baseChangeGaloisModel hM b hb v hv).generic)
    ((baseChangeHom hM b hb v hv).traitChangeThickening (traitGenericField K)
      (baseChangeTotalStructure hM b hb v hv) q g hM.isPullback_j.w
      (baseChangeHom_total_comp hM b hb v hv) ≫ pullback.fst _ _)
    M.ε (baseChangeGaloisModel hM b hb v hv).ε (Category.assoc _ _ _)
    (Profinite.padicAlgClRingObj ℓ) A hA
  -- Direct elimination keeps the large dependent types in their original form.
  refine (exists_integralModel_baseChangeGaloisModel hM b hb v hv hB eB
    (by cast_proofs hC)).elim fun E hE ↦ ?_
  refine hE.elim fun K₀ hK₀ ↦ ?_
  refine hK₀.elim fun e htors ↦ ?_
  refine ((baseChangeGaloisModel hM b hb v hv)
    |>.exists_retraction_pullbackExchange_galoisLayerHom_of_integralModel
      (L := traitTensorCompositum (PowerSeries K) (traitGenericField k') (traitGenericField K))
      (baseChangeGaloisResidue hM b hb v hv)
      (traitTensorCompositumSep (PowerSeries K) (traitGenericField k') (traitGenericField K)) ℓ
      (fun M' _ ↦ IntermediateField.not_dvd_finrank_of_forall_finiteGalois
        (L := traitTensorCompositum (PowerSeries K) (traitGenericField k') (traitGenericField K))
        (Ω := traitTensorCompositumSep (PowerSeries K) (traitGenericField k') (traitGenericField K))
        (not_dvd_finrank_traitTensorCompositum (k' := k') (K := K)
          (Fact.out : ringChar k' ≠ ℓ) Fact.out) M')
      A (by cast_proofs hC) E K₀ e htors).elim fun L₁ hL₁ ↦ ?_
  have result := exists_subgroup_pullbackExchange_of_galois_average
    (Λ := Profinite.padicAlgClRingObj ℓ)
    (ρ := baseChangeToGaloisLayer hM b hb v hv)
    (ψ := ((baseChangeGaloisModel hM b hb v hv).galoisLayerHom
          (baseChangeGaloisResidue hM b hb v hv)
          (traitTensorCompositumSep (PowerSeries K) (traitGenericField k') (traitGenericField K))))
    (χ := (((baseChangeHom hM b hb v hv).traitChangeModelHom (traitGenericField K)
          (baseChangeTotalStructure hM b hb v hv) q g hM.isPullback_j.w
          (baseChangeHom_total_comp hM b hb v hv)).comp
            (baseChangeHom hM b hb v hv).fromCartesian))
    (φ := baseChangeHom hM b hb v hv) (A := A)
    (hχ := by
      exact isIso_pullbackExchange_app_of_model_eq
        (M₀ := (baseChangeHom hM b hb v hv).traitChangeModel (traitGenericField K)
          (baseChangeTotalStructure hM b hb v hv) q g hM.isPullback_j.w
          (baseChangeHom_total_comp hM b hb v hv))
        (M₁ := baseChangeGaloisModel hM b hb v hv)
        (Profinite.padicAlgClRingObj ℓ)
        (((baseChangeHom hM b hb v hv).traitChangeModelHom (traitGenericField K)
          (baseChangeTotalStructure hM b hb v hv) q g hM.isPullback_j.w
          (baseChangeHom_total_comp hM b hb v hv)).comp
            (baseChangeHom hM b hb v hv).fromCartesian)
        (((baseChangeHom hM b hb v hv).traitChangeModelHom (traitGenericField K)
          (baseChangeTotalStructure hM b hb v hv) q g hM.isPullback_j.w
          (baseChangeHom_total_comp hM b hb v hv)).comp
            (baseChangeHom hM b hb v hv).fromCartesian) rfl HEq.rfl A (by cast_proofs hM1))
    (htot := baseChangeToGaloisModel_comp_total hM b hb v hv)
    (hgen := baseChangeToGaloisModel_comp_generic hM b hb v hv)
    (hρ := isIso_pullbackExchange_baseChangeToGaloisLayer hM b hb v hv _)
    (act := baseChangeAut hM b hb v hv)
    (eG := GenericAut.galoisEquiv (k' := k') (K := K)) (L₁ := L₁)
    (actΩ := ((baseChangeGaloisModel hM b hb v hv).galoisLayerAut
          (baseChangeGaloisResidue hM b hb v hv)
          (traitTensorCompositumSep (PowerSeries K) (traitGenericField k') (traitGenericField K))))
    (hmul := autAction_baseChangeAut_mul hM b hb v hv _)
    (hint := pullbackExchange_baseChangeToGaloisLayer_app_comp_autAction_symm hM b hb v hv _)
    (htriv := hL₁.1)
    (hSA := by
      exact galois_average_of_model_eq
        (M₀ := (baseChangeGaloisModel hM b hb v hv).galoisLayer
          (baseChangeGaloisResidue hM b hb v hv)
          (traitTensorCompositumSep (PowerSeries K) (traitGenericField k') (traitGenericField K)))
        (M₁ := baseChangeGaloisLayer hM b hb v hv)
        (Profinite.padicAlgClRingObj ℓ) L₁
        ((baseChangeGaloisModel hM b hb v hv).galoisLayerHom
          (baseChangeGaloisResidue hM b hb v hv)
          (traitTensorCompositumSep (PowerSeries K) (traitGenericField k') (traitGenericField K)))
        ((baseChangeGaloisModel hM b hb v hv).galoisLayerHom
          (baseChangeGaloisResidue hM b hb v hv)
          (traitTensorCompositumSep (PowerSeries K) (traitGenericField k') (traitGenericField K)))
        ((baseChangeGaloisModel hM b hb v hv).galoisLayerAut
          (baseChangeGaloisResidue hM b hb v hv)
          (traitTensorCompositumSep (PowerSeries K) (traitGenericField k') (traitGenericField K)))
        ((baseChangeGaloisModel hM b hb v hv).galoisLayerAut
          (baseChangeGaloisResidue hM b hb v hv)
          (traitTensorCompositumSep (PowerSeries K) (traitGenericField k') (traitGenericField K)))
        rfl HEq.rfl HEq.rfl A
        (by cast_proofs hL₁.2))
  cast_proofs result

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
