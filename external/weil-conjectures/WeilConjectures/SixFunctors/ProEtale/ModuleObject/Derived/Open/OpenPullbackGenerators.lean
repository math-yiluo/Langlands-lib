/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
public import WeilConjectures.CategoryTheory.SixFunctors.Monoidal

/-!
# Open inverse image preserves the constructible finite-Tor generators

Source: blueprint main-20261015, proposition-composition-open-restriction-compactifications-f, proof
step 3; sk-prop-proper-base-change-unbounded-pullback, proof steps 1--5.
(blueprint: lem-sfb-open-pullback-generators)
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem pullbackPointModelIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U X : Scheme.{u}} (j : U ⟶ X)
    (P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) :
    Nonempty ((upperStar Λ j).obj (((upperStarFromPoint X).mapMod Λ).obj P) ≅
      ((upperStarFromPoint U).mapMod Λ).obj P) := by
  refine ⟨?_⟩
  let α := condensedPullbackHom Λ j
  exact (Mod.extendScalars α).mapIso
    ((Functor.mapModCompIso (upperStarFromPoint X) (ProEtale.upperStar Ab.{u + 1} j)
      (upperStarFromPointComp j).hom Λ).app P) ≪≫
    (Mod.extendScalarsIsoComapInv α).app _ ≪≫
    (Mod.comapEquivalenceOfIsIso α).unitIso.symm.app _

private theorem model_of_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (h : HasFiniteConstantLocalModel Λ X M) :
    HasFiniteConstantLocalModel Λ X N := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := hC i
  exact ⟨P, hP, ⟨(upperStar Λ (C.f i)).mapIso e.symm ≪≫ eP⟩⟩

private noncomputable def squarePullbackIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {A B C D : Scheme.{u}}
    (a : A ⟶ B) (b : A ⟶ C) (c : B ⟶ D) (d : C ⟶ D) (h : a ≫ c = b ≫ d)
    (M : Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1}) (condensedRingObj Λ D)) :
    (upperStar Λ a).obj ((upperStar Λ c).obj M) ≅
      (upperStar Λ b).obj ((upperStar Λ d).obj M) :=
  ((upperStarComp Λ a c).app M).symm ≪≫
    (eqToIso (congrArg (upperStar Λ) h)).app M ≪≫ (upperStarComp Λ b d).app M

private theorem pullbackLocalModel
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {W Z X Y : Scheme.{u}}
    (f : Z ⟶ X) (g : Y ⟶ X) (a : W ⟶ Z) (b : W ⟶ Y) (hab : b ≫ g = a ≫ f)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : ∃ P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ,
      Mod.IsFinitelyPresented Λ P ∧ Nonempty ((upperStar Λ f).obj M ≅
        ((upperStarFromPoint Z).mapMod Λ).obj P)) :
    ∃ P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ,
      Mod.IsFinitelyPresented Λ P ∧
      Nonempty ((upperStar Λ b).obj ((upperStar Λ g).obj M) ≅
        ((upperStarFromPoint W).mapMod Λ).obj P) := by
  obtain ⟨P, hP, ⟨eP⟩⟩ := h
  obtain ⟨eModel⟩ := pullbackPointModelIso Λ a P
  exact ⟨P, hP, ⟨squarePullbackIso Λ b a g f hab M ≪≫
    (upperStar Λ a).mapIso eP ≪≫ eModel⟩⟩

private theorem model_of_cover_square
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (g : Y ⟶ X)
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (D : Scheme.Cover.{u} Scheme.proetalePrecoverage Y)
    (idx : D.I₀ → C.I₀) (a : ∀ i, D.X i ⟶ C.X (idx i))
    (hab : ∀ i, D.f i ≫ g = a i ≫ C.f (idx i))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hC : ∀ i : C.I₀,
      ∃ P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ,
        Mod.IsFinitelyPresented Λ P ∧ Nonempty ((upperStar Λ (C.f i)).obj M ≅
          ((upperStarFromPoint (C.X i)).mapMod Λ).obj P)) :
    HasFiniteConstantLocalModel Λ Y ((upperStar Λ g).obj M) := by
  exact ⟨D, fun i ↦ pullbackLocalModel Λ (C.f (idx i)) g (a i) (D.f i)
    (hab i) M (hC (idx i))⟩

private theorem pullbackCover_exists {X Y : Scheme.{u}} (g : Y ⟶ X)
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage X) :
    ∃ (D : Scheme.Cover.{u} Scheme.proetalePrecoverage Y)
      (idx : D.I₀ → C.I₀) (a : ∀ i, D.X i ⟶ C.X (idx i)),
      ∀ i, D.f i ≫ g = a i ≫ C.f (idx i) := by
  exact ⟨C.pullback₁ g, id, fun i ↦ pullback.snd g (C.f i),
    fun i ↦ pullback.condition⟩

private theorem model_pullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (g : Y ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : HasFiniteConstantLocalModel Λ X M) :
    HasFiniteConstantLocalModel Λ Y ((upperStar Λ g).obj M) := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨D, idx, a, hab⟩ := pullbackCover_exists g C
  exact model_of_cover_square Λ g C D idx a hab M hC

private theorem pullbackStratification_exists {X Y : Scheme.{u}} (g : Y ⟶ X)
    (S : Scheme.Stratification X) :
    ∃ (T : Scheme.Stratification Y) (idx : Fin T.n → Fin S.n)
      (a : ∀ i, T.domain i ⟶ S.domain (idx i)),
      ∀ i, T.immersion i ≫ g = a i ≫ S.immersion (idx i) := by
  exact ⟨S.pullback g, id, fun i ↦ pullback.fst (S.immersion i) g,
    fun i ↦ pullback.condition.symm⟩

private theorem stratified_pullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (g : Y ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : IsFiniteConstantStratified Λ X M) :
    IsFiniteConstantStratified Λ Y ((upperStar Λ g).obj M) := by
  obtain ⟨S, hS⟩ := h
  obtain ⟨T, idx, a, ha⟩ := pullbackStratification_exists g S
  refine ⟨T, fun i ↦ ?_⟩
  exact model_of_iso Λ
    (squarePullbackIso Λ (a i) (T.immersion i) (S.immersion (idx i)) g (ha i).symm M)
    (model_pullback Λ (a i) _ (hS (idx i)))

private theorem constructible_of_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (h : IsConstantModelConstructible Λ X M) :
    IsConstantModelConstructible Λ X N := by
  classical
  unfold IsConstantModelConstructible at h ⊢
  split_ifs at h ⊢ with hX
  · obtain ⟨S, hS⟩ := h
    exact ⟨S, fun a ↦ model_of_iso Λ ((upperStar Λ (S.immersion a)).mapIso e) (hS a)⟩
  · intro U hU
    obtain ⟨S, hS⟩ := h U hU
    exact ⟨S, fun a ↦ model_of_iso Λ
      ((upperStar Λ (S.immersion a)).mapIso ((upperStar Λ U.ι).mapIso e)) (hS a)⟩

/-- The exact termwise open pullback preserves the bounded constructible finite-Tor
generators for every admissible condensed coefficient, including coefficients given up to
ring-object isomorphism.
Source: blueprint proposition-composition-open-restriction-compactifications-f, proof step 3; the
inverse-image localizing argument of sk-prop-proper-base-change-unbounded-pullback.
(blueprint: lem-sfb-open-pullback-generators).

Proof: Give U its structure morphism j followed by the structure morphism of X. These
schemes are qcqs: X is separated of finite type over a field, and j is quasi-compact open.
Exact module inverse image commutes with cohomology, preserves all sums by its direct-image
adjunction, and is triangulated on the ordinary unbounded derived categories. Pull back
the finite constructible stratification and each constant-model trivializing cover of a
Dctf generator. The coefficient compositor identifies each pulled-back model with the
same finitely presented module on the point, so it stays constructible. Exactness keeps
its cohomological bounds. The existing upperStar_preservesFlat theorem shows that inverse
image sends flat modules to flat modules. For a Tor interval [a,b], apply
DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj: an exact functor preserving flat
objects sends a flat model supported in [a,b] to one supported in the same interval. Thus
pullback sends every Dctf generator into Dctf, including when U is empty. The finite presentation
models are on the point before restriction, so their scalar matrices remain the same
under the canonical coefficient compositor. This argument applies directly to Λ and
therefore includes the ring-object isomorphism convention of admissibility.
-/
theorem openPullback_generators
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (p : ℕ) [CharP k p] (_hp : 0 < p) (_hpℓ : p ≠ ℓ)
    (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {U X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] :
    ∀ K : ConstantModelConstructibleFiniteTor Λ X,
      constantModelBoundedConstructible Λ U
          ((upperStar Λ j).mapDerivedCategory.obj K.obj) ∧
        DerivedCategory.finiteTorAmplitude _ ((upperStar Λ j).mapDerivedCategory.obj K.obj) := by
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : QuasiSeparatedSpace X := inferInstance
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace j
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian j
  have : QuasiSeparatedSpace U := inferInstance
  intro K
  refine ⟨⟨(upperStar Λ j).bounded_mapDerivedCategory_obj K.property.1.1, ?_⟩, ?_⟩
  · intro n
    apply constructible_of_iso Λ
      (((upperStar Λ j).mapDerivedCategoryHomologyFunctorIso n).app K.obj)
    have h := K.property.1.2 n
    have hX : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
    have hU : CompactSpace U ∧ QuasiSeparatedSpace U := ⟨inferInstance, inferInstance⟩
    simp only [IsConstantModelConstructible, ite_eq_left hX] at h
    simp only [IsConstantModelConstructible, ite_eq_left hU]
    exact stratified_pullback Λ j _ h
  · have hflat := upperStar_preservesFlat Λ j
    obtain ⟨a, b, hab⟩ := K.property.2
    exact ⟨a, b, DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj (upperStar Λ j) hab⟩

end AlgebraicGeometry.ProEtale.CondensedRing
