/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.GaloisInvariantsProjector
public import WeilConjectures.SixFunctors.NearbyCycles.GaloisLayerStabilization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOriginUpperStar

/-!

# Stabilization of a Galois layer from the triviality of the Galois action

Let `N` be a model of `X` with special fibre `X'`, `h : N.generic ⟶ Spec L`, `Ω/L` a Galois
extension whose finite subextensions have degrees invertible in a finite discrete commutative
ring `T₀`, `Λ = C(-, T₀)` and `L ⊆ L' ⊆ Ω` with `L'/L` finite. If the subgroup `Gal(Ω/L')` acts
trivially on the cohomology sheaves of `Ψ_{N_Ω} (L(𝟙)^* C)`, then the pullback exchange of the
change of Galois layers `N_Ω ⟶ N_{L'}` (`NearbyCyclesModel.galoisLayerRestrict`) is invertible
at `L(𝟙)^* C` (`NearbyCyclesModel.isIso_pullbackExchange_galoisLayerRestrict_of_homology`): the
nearby cycles stabilize at the level `L'`.

The Galois layer `N_Ω` is identified with the Galois layer `(N_{L'})_Ω` of `N_{L'}` over `L'`
(`NearbyCyclesModel.galoisLayerTower`, whose exchange is invertible and intertwines the Galois
actions), through which the change of Galois layers becomes the projection `(N_{L'})_Ω ⟶ N_{L'}`.
By the projector onto the `Gal(Ω/L')`-invariants
(`NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom_of_plusEtaleOrigin_projector`
for `N_{L'}`), the exchange of this projection is a split monomorphism whose idempotent is the
identity on cohomology sheaves, hence an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

/-- If `F ≅ 𝟭` and `H` kills the endomorphism `x` (`H.map x = 𝟙`), then `H` kills `F.map x`. -/
lemma map_map_eq_id_of_iso_id {C A : Type*} [Category C] [Category A] {F : C ⥤ C}
    (I : F ≅ 𝟭 C) (H : C ⥤ A) {P : C} {x : P ⟶ P} (hx : H.map x = 𝟙 _) :
    H.map (F.map x) = 𝟙 _ := by
  rw [← NatIso.naturality_2 I x]
  simp [hx]

/-- If `H` kills `y` and `e ≫ x = y' ≫ e` with `e` an isomorphism and `H.map y' = 𝟙`, then `H`
kills `x`. -/
lemma map_eq_id_of_comp_eq_comp {C A : Type*} [Category C] [Category A] (H : C ⥤ A) {P Q : C}
    {x : Q ⟶ Q} {y : P ⟶ P} (e : P ⟶ Q) [IsIso e] (he : e ≫ x = y ≫ e) (hy : H.map y = 𝟙 _) :
    H.map x = 𝟙 _ := by
  rw [← cancel_epi (H.map e), ← H.map_comp, he, H.map_comp, hy, Category.id_comp,
    Category.comp_id]

/-- A split monomorphism `α` (`α ≫ r = 𝟙`) whose idempotent `r ≫ α` is sent to the identity by
`H` is sent to an isomorphism by `H`. -/
lemma isIso_map_of_comp_eq_id {C A : Type*} [Category C] [Category A] (H : C ⥤ A) {P Q : C}
    {α : P ⟶ Q} {r : Q ⟶ P} (hr : α ≫ r = 𝟙 _) (hrα : H.map (r ≫ α) = 𝟙 _) :
    IsIso (H.map α) :=
  ⟨H.map r, by rw [← H.map_comp, hr, H.map_id], by rw [← H.map_comp, hrα]⟩

/-- If `F ≅ 𝟭` and `χ ≫ m = c ≫ F.map ρ ≫ e` with `χ`, `m`, `c`, `e` isomorphisms, then `ρ` is an
isomorphism. -/
lemma isIso_of_comp_eq_comp_map_comp {D : Type*} [Category D] {F : D ⥤ D} (I : F ≅ 𝟭 D)
    {A B B' P Q : D} {χ : A ⟶ B} {m : B ⟶ B'} {c : A ⟶ F.obj P} {ρ : P ⟶ Q} {e : F.obj Q ⟶ B'}
    [IsIso χ] [IsIso m] [IsIso c] [IsIso e] (h : χ ≫ m = c ≫ F.map ρ ≫ e) : IsIso ρ := by
  have hρ : F.map ρ = inv c ≫ χ ≫ m ≫ inv e := by
    rw [IsIso.eq_inv_comp, ← Category.assoc χ, IsIso.eq_comp_inv, Category.assoc]
    exact h.symm
  have : IsIso (F.map ρ) := by
    rw [hρ]
    infer_instance
  exact (NatIso.isIso_map_iff I ρ).1 this

/-- A split map is invertible if its projector is the identity on homology after a functor
isomorphic to the identity. -/
private lemma isIso_of_split_of_homology_map_comp_eq_id {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] {F : DerivedCategory A ⥤ DerivedCategory A} (I : F ≅ 𝟭 _)
    {P Q : DerivedCategory A} {α : P ⟶ Q} {r : Q ⟶ P} (hr : α ≫ r = 𝟙 _)
    (h : ∀ q : ℤ, (DerivedCategory.homologyFunctor A q).map (F.map (r ≫ α)) ≫ 𝟙 _ = 𝟙 _) :
    IsIso α :=
  (NatIso.isIso_map_iff I α).1 ((DerivedCategory.isIso_iff _ _).2 fun q ↦
    isIso_map_of_comp_eq_id (F ⋙ DerivedCategory.homologyFunctor A q) hr
      ((Category.comp_id _).symm.trans (h q)))

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {X X' : Scheme.{u}} (N : NearbyCyclesModel X X') {L : Type u} [Field L]
  (h : N.generic ⟶ Spec (.of L)) (Ω : Type u) [Field Ω] [Algebra L Ω]
  (L' : IntermediateField L Ω)

lemma ringHomId_comp_algebraMap_intermediateField :
    (RingHom.id Ω).comp (algebraMap L Ω) = (algebraMap L' Ω).comp (algebraMap L L') := by
  rw [RingHom.id_comp, ← IsScalarTower.algebraMap_eq]

/-- The identification of the Galois layer `(N_{L'})_Ω` of the finite layer `N_{L'}` (over `L'`)
with the Galois layer `N_Ω`, over the identities: the change of Galois layers
(`NearbyCyclesModel.galoisLayerMap`) of the projection `N_{L'} ⟶ N` and the identity of `Ω`. -/
noncomputable def galoisLayerTower :
    ((N.galoisLayer h L').galoisLayer (pullback.snd _ _) Ω).Hom (N.galoisLayer h Ω) (𝟙 X)
      (𝟙 X') :=
  galoisLayerMap Ω Ω (RingHom.id Ω) (ringHomId_comp_algebraMap_intermediateField Ω L')
    (N.galoisLayerHom h L') pullback.condition

instance isIso_galoisLayerTower_total : IsIso (N.galoisLayerTower h Ω L').total := by
  rw [galoisLayerTower, galoisLayerMap_total, galoisLayerHom_total]
  exact IsIso.id _

/-- The generic fibres of `(N_{L'})_Ω` and `N_Ω` are identified by pasting of pullback squares. -/
instance isIso_galoisLayerTower_generic : IsIso (N.galoisLayerTower h Ω L').generic := by
  have hpaste := (IsPullback.of_hasPullback (pullback.snd h
    (Spec.map (CommRingCat.ofHom (algebraMap L L')))) (Spec.map (CommRingCat.ofHom
      (algebraMap L' Ω)))).paste_horiz (IsPullback.of_hasPullback h
        (Spec.map (CommRingCat.ofHom (algebraMap L L'))))
  rw [specMap_algebraMap_intermediateField] at hpaste
  have heq : (N.galoisLayerTower h Ω L').generic = hpaste.isoPullback.hom := by
    refine pullback.hom_ext ?_ ?_
    · simp [galoisLayerTower]
    · simp [galoisLayerTower]
  rw [heq]
  infer_instance

/-- The identification `(N_{L'})_Ω ≅ N_Ω` followed by the change of Galois layers `N_Ω ⟶ N_{L'}`
is the projection `(N_{L'})_Ω ⟶ N_{L'}` on generic fibres. -/
lemma galoisLayerTower_generic_comp_galoisLayerRestrict_generic :
    (N.galoisLayerTower h Ω L').generic ≫ (N.galoisLayerRestrict h Ω L').generic =
      ((N.galoisLayer h L').galoisLayerHom (pullback.snd _ _) Ω).generic := by
  refine pullback.hom_ext ?_ ?_ <;> simp [galoisLayerTower]

/-- The identification `(N_{L'})_Ω ≅ N_Ω` is equivariant for `Gal(Ω/L') ⊆ Gal(Ω/L)` on generic
fibres. -/
lemma galoisLayerAut_generic_comp_galoisLayerTower_generic (σ : Ω ≃ₐ[L'] Ω) :
    ((N.galoisLayer h L').galoisLayerAut (pullback.snd _ _) Ω σ).generic ≫
        (N.galoisLayerTower h Ω L').generic =
      (N.galoisLayerTower h Ω L').generic ≫
        (N.galoisLayerAut h Ω (σ.restrictScalars L)).generic := by
  refine pullback.hom_ext ?_ ?_
  · simp [galoisLayerTower]
  · simp only [galoisLayerAut_generic, galoisLayerTower, galoisLayerMap_generic, Category.assoc,
      galoisLayerGenericMap_snd, pullbackAction_snd_assoc, galoisLayerGenericMap_snd_assoc,
      pullbackAction_snd]
    congr 1
    rw [specGaloisAction, specGaloisAction, ← Spec.map_comp, ← Spec.map_comp]
    rfl

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The exchange of the identification `(N_{L'})_Ω ≅ N_Ω` intertwines the Galois actions of
`σ ∈ Gal(Ω/L')` and of `σ` viewed in `Gal(Ω/L)`. -/
lemma pullbackExchange_galoisLayerTower_app_comp_galoisLayerAction (σ : Ω ≃ₐ[L'] Ω)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    ((N.galoisLayerTower h Ω L').pullbackExchange Λ).app C ≫
        (N.galoisLayer h L').galoisLayerAction Λ (pullback.snd _ _) Ω σ (L((𝟙 X)^*⟦Λ⟧).obj C) =
      L((𝟙 X')^*⟦Λ⟧).map (N.galoisLayerAction Λ h Ω (σ.restrictScalars L) C) ≫
        ((N.galoisLayerTower h Ω L').pullbackExchange Λ).app C :=
  Hom.pullbackExchange_app_comp_autAction_of_comm Λ _ _ _ (by simp [galoisLayerTower])
    (N.galoisLayerAut_generic_comp_galoisLayerTower_generic h Ω L' σ) C

/-- The composition law for `(N_{L'})_Ω ≅ N_Ω ⟶ N_{L'}`. -/
lemma pullbackExchange_galoisLayerHom_galoisLayerTower_app
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (((N.galoisLayer h L').galoisLayerHom (pullback.snd _ _) Ω).pullbackExchange Λ).app C ≫
        (((N.galoisLayer h L').galoisLayer (pullback.snd _ _) Ω).nearbyCycles Λ).map
          ((leftDerivedUpperStarCompOfEq Λ (Category.id_comp (𝟙 X))).hom.app C) =
      (leftDerivedUpperStarCompOfEq Λ (Category.id_comp (𝟙 X'))).hom.app
          (((N.galoisLayer h L').nearbyCycles Λ).obj C) ≫
        L((𝟙 X')^*⟦Λ⟧).map (((N.galoisLayerRestrict h Ω L').pullbackExchange Λ).app C) ≫
        ((N.galoisLayerTower h Ω L').pullbackExchange Λ).app (L((𝟙 X)^*⟦Λ⟧).obj C) :=
  (N.galoisLayerTower h Ω L').pullbackExchange_comp_app_of_eq Λ (N.galoisLayerRestrict h Ω L')
    _ (Category.id_comp (𝟙 X)) (Category.id_comp (𝟙 X')) (Category.id_comp _)
    (N.galoisLayerTower_generic_comp_galoisLayerRestrict_generic h Ω L') C

variable (T₀ : Type) [TopologicalSpace T₀] [CommRing T₀] [IsTopologicalRing T₀]
  [DiscreteTopology T₀] [Finite T₀]

/-- **Stabilization of the nearby cycles of a Galois layer from the triviality of the Galois
action on cohomology** (torsion coefficients in which the degrees of the finite subextensions
of `Ω/L` are invertible). Let `L ⊆ L' ⊆ Ω` with `L'/L` finite and `Lε^* C` bounded below of étale
origin. If every `σ ∈ Gal(Ω/L')` acts trivially on the cohomology sheaves of
`Ψ_{N_Ω} (L(𝟙)^* C)`, then the pullback exchange of the change of Galois layers `N_Ω ⟶ N_{L'}`
is invertible at `L(𝟙)^* C`. -/
theorem isIso_pullbackExchange_galoisLayerRestrict_of_homology [IsGalois L Ω]
    [QuasiCompact N.j] [QuasiSeparated N.j] [FiniteDimensional L L']
    (hp : ∀ M : IntermediateField L Ω, FiniteDimensional L M →
      IsUnit ((Module.finrank L M : ℕ) : T₀))
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) X)))
    (hC : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T₀)) N.generic
      ((finiteCoefficientDerivedEquivalence N.generic T₀).functor.obj
        (L((N.ε)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)))
    (htriv : ∀ (q : ℤ) (σ : Ω ≃ₐ[L] Ω), σ ∈ L'.fixingSubgroup →
      (DerivedCategory.homologyFunctor _ q).map
        (N.galoisLayerAction (Profinite.continuousMapRingObj T₀) h Ω σ
          (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)) = 𝟙 _) :
    IsIso (((N.galoisLayerRestrict h Ω L').pullbackExchange
      (Profinite.continuousMapRingObj T₀)).app
        (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)) := by
  -- the finite layer `N_{L'}` satisfies the hypotheses of the projector theorem over `L'`
  have : QuasiCompact (N.galoisLayer h L').j := by
    dsimp [galoisLayer]
    infer_instance
  have : QuasiSeparated (N.galoisLayer h L').j := by
    dsimp [galoisLayer]
    infer_instance
  have hp₁ (M : FiniteGaloisIntermediateField L' Ω) :
      IsUnit ((Module.finrank L' M : ℕ) : T₀) := by
    have hfin : FiniteDimensional L M := Module.Finite.trans L' M
    have := Module.Free.of_divisionRing L' M
    have hM := hp (M.toIntermediateField.restrictScalars L) hfin
    change IsUnit ((Module.finrank L M : ℕ) : T₀) at hM
    rw [← Module.finrank_mul_finrank L L' M, Nat.cast_mul] at hM
    exact isUnit_of_mul_isUnit_right hM
  have hC₁ := ObjectProperty.prop_of_iso _
    ((finiteCoefficientDerivedEquivalence _ T₀).functor.mapIso
      ((leftDerivedUpperStarComp (Profinite.continuousMapRingObj T₀) (pullback.fst h
        (Spec.map (CommRingCat.ofHom (algebraMap L L')))) N.ε).symm.app C ≪≫
      (leftDerivedUpperStarCompOfEq (Profinite.continuousMapRingObj T₀)
        (Category.comp_id (pullback.fst h
          (Spec.map (CommRingCat.ofHom (algebraMap L L'))) ≫ N.ε))).app C))
    (plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj T₀
      (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L L')))) hC)
  obtain ⟨r, hr, -, hproj⟩ :=
    exists_retraction_pullbackExchange_galoisLayerHom_of_plusEtaleOrigin_projector
      (N.galoisLayer h L') (pullback.snd _ _) Ω T₀ hp₁ _ hC₁
  -- the identification `(N_{L'})_Ω ≅ N_Ω` has an invertible exchange intertwining the actions
  have : IsIso ((N.galoisLayerTower h Ω L').pullbackExchange (Profinite.continuousMapRingObj T₀)) :=
    Hom.isIso_pullbackExchange_of_isIso _ _
  have hact (σ : Ω ≃ₐ[L'] Ω) (q : ℤ) :=
    map_map_eq_id_of_iso_id (leftDerivedUpperStarId (Profinite.continuousMapRingObj T₀) X')
      (DerivedCategory.homologyFunctor _ q)
      (map_eq_id_of_comp_eq_comp (DerivedCategory.homologyFunctor _ q) _
        (N.pullbackExchange_galoisLayerTower_app_comp_galoisLayerAction h Ω L'
          (Profinite.continuousMapRingObj T₀) σ _)
        (map_map_eq_id_of_iso_id (leftDerivedUpperStarId (Profinite.continuousMapRingObj T₀) X') _
          (htriv q _ ((IntermediateField.mem_fixingSubgroup_iff L' _).2 fun x hx ↦
            σ.commutes ⟨x, hx⟩))))
  -- the exchange of the projection `(N_{L'})_Ω ⟶ N_{L'}` is invertible: its idempotent is the
  -- identity on cohomology sheaves
  have hfix (q : ℤ) := hproj (𝟙 X') q (𝟙 _) (fun σ : Ω ≃ₐ[L'] Ω ↦ σ)
    (fun M a ↦ ⟨a.liftNormal Ω, fun x ↦ a.liftNormal_commutes Ω x⟩)
    (fun σ ↦ (Category.comp_id _).trans (hact σ q))
  have := isIso_of_split_of_homology_map_comp_eq_id
    (leftDerivedUpperStarId (Profinite.continuousMapRingObj T₀) X') hr hfix
  -- composition law for `(N_{L'})_Ω ⟶ N_Ω ⟶ N_{L'}`
  have hcomp := N.pullbackExchange_galoisLayerHom_galoisLayerTower_app h Ω L' _
    (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)
  exact isIso_of_comp_eq_comp_map_comp (leftDerivedUpperStarId _ X') hcomp

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
