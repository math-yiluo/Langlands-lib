/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.WeaklyEtaleBaseChange

/-!
# Descent of subobjects along finite families of weakly étale maps, as a kernel

Let `Λ` be a commutative condensed ring, `S` a scheme, `M` a module object over `Λ_S` and
`f_k : V_k ⟶ S` a finite family of weakly étale morphisms. Suppose given, for each `k`, a
morphism `π_k : f_k^* M ⟶ Q_k` (think of the cokernel of a subobject `F_k ⊆ f_k^* M`) such that
on fibre products `P_{jk} = V_j ×_S V_k` (given by cartesian squares `p₁ ≫ f_j = p₂ ≫ f_k`) the
pullbacks of `π_j` and of `π_k` agree up to an isomorphism, through the canonical identification
`p₁^* f_j^* M ≅ p₂^* f_k^* M`. Then the kernel
```
K = ker (M ⟶ ∏_k f_{k*} Q_k)
```
of the adjoints of the `π_k` satisfies `f_j^* K = ker π_j` for every `j`
(`ProEtale.CondensedRing.exists_iso_upperStar_kernel_kernelDescentMap`). In other words,
compatible subobjects of the pullbacks `f_k^* M` descend to a subobject of `M`, without any
gluing theory.

The proof uses weakly étale base change `f_j^* f_{k*} ≅ p₁_* p₂^*`
(`ProEtale.CondensedRing.isIso_lowerStarBaseChange_of_isPullback`) and that the pullback along
`p₁ : V_j ×_S V_j ⟶ V_j` is faithful, `p₁` having the diagonal as a section.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace CategoryTheory.Adjunction

variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']

/-- The image of a unit under `G`, followed by the exchange morphism, is the unit followed by the
image of the comparison isomorphism. -/
lemma map_unit_app_comp_exchangeRight_app {Lf : B ⥤ A} {Rf : A ⥤ B} {Lf' : B' ⥤ A'}
    {Rf' : A' ⥤ B'} {G : B ⥤ B'} {G' : A ⥤ A'} (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf')
    (θ : G ⋙ Lf' ≅ Lf ⋙ G') (N : B) :
    G.map (af.unit.app N) ≫ (exchangeRight af af' θ).app (Lf.obj N) =
      af'.unit.app (G.obj N) ≫ Rf'.map (θ.hom.app N) := by
  rw [exchangeRight_app]
  have h₁ := af'.unit.naturality (G.map (af.unit.app N))
  have h₂ := θ.hom.naturality (af.unit.app N)
  simp only [Functor.id_map, Functor.comp_map] at h₁ h₂
  rw [reassoc_of% h₁, ← Rf'.map_comp, ← Rf'.map_comp, reassoc_of% h₂, ← G'.map_comp,
    af.left_triangle_components, G'.map_id, Category.comp_id]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- For weakly étale `f_j` and a cartesian square `p₁ ≫ f_j = p₂ ≫ f_k`, a morphism
`u : T ⟶ f_j^* M` kills the pullback of the adjoint `M ⟶ f_{k*} Q` of `π : f_k^* M ⟶ Q` if and
only if its pullback along `p₁` kills the pullback of `π`, through `p₁^* f_j^* ≅ p₂^* f_k^*`. -/
lemma comp_upperStar_map_unit_eq_zero_iff {S V W P : Scheme.{u}} {fj : V ⟶ S} {fk : W ⟶ S}
    {p₁ : P ⟶ V} {p₂ : P ⟶ W} (hP : IsPullback p₁ p₂ fj fk) [WeaklyEtale fj]
    {M : Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)}
    {Q : Mod (Sheaf (ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W)}
    (π : (fk)^*⟦Λ⟧.obj M ⟶ Q)
    {T : Mod (Sheaf (ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V)}
    (v : T ⟶ (fj)^*⟦Λ⟧.obj M) :
    v ≫ (fj)^*⟦Λ⟧.map ((upperStarLowerStarAdjunction Λ fk).unit.app M ≫ (fk)_*⟦Λ⟧.map π) = 0 ↔
      (p₁)^*⟦Λ⟧.map v ≫ (upperStarSquareComparison Λ hP.flip.toCommSq).hom.app M ≫
        (p₂)^*⟦Λ⟧.map π = 0 := by
  have : WeaklyEtale p₂ :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @WeaklyEtale) hP ‹_›
  have hiso := isIso_lowerStarBaseChange_of_isPullback Λ hP.flip
  have e : (fj)^*⟦Λ⟧.map ((upperStarLowerStarAdjunction Λ fk).unit.app M ≫ (fk)_*⟦Λ⟧.map π) ≫
      (lowerStarBaseChange Λ hP.flip.toCommSq).app Q =
      (upperStarLowerStarAdjunction Λ p₁).unit.app _ ≫
        (p₁)_*⟦Λ⟧.map ((upperStarSquareComparison Λ hP.flip.toCommSq).hom.app M ≫
          (p₂)^*⟦Λ⟧.map π) := by
    have hn := (lowerStarBaseChange Λ hP.flip.toCommSq).naturality π
    simp only [Functor.comp_map] at hn
    rw [Functor.map_comp, Category.assoc, hn, lowerStarBaseChange_eq, ← Category.assoc,
      Adjunction.map_unit_app_comp_exchangeRight_app, Category.assoc, ← Functor.map_comp]
  have hb : IsIso ((lowerStarBaseChange Λ hP.flip.toCommSq).app Q) :=
    NatIso.isIso_app_of_isIso _ _
  rw [← cancel_mono ((lowerStarBaseChange Λ hP.flip.toCommSq).app Q), zero_comp,
    Category.assoc, e, ← Category.assoc]
  set adj := upperStarLowerStarAdjunction Λ p₁
  have h : (v ≫ adj.unit.app ((fj)^*⟦Λ⟧.obj M)) ≫ (p₁)_*⟦Λ⟧.map
      ((upperStarSquareComparison Λ hP.flip.toCommSq).hom.app M ≫ (p₂)^*⟦Λ⟧.map π) =
      adj.homEquiv _ _ ((p₁)^*⟦Λ⟧.map v ≫
        (upperStarSquareComparison Λ hP.flip.toCommSq).hom.app M ≫ (p₂)^*⟦Λ⟧.map π) := by
    rw [adj.homEquiv_naturality_left, adj.homEquiv_unit, Category.assoc]
  have hz : adj.homEquiv T ((p₂)^*⟦Λ⟧.obj Q) 0 = 0 := by
    simp [adj.homEquiv_unit]
  rw [h, ← hz]
  exact (adj.homEquiv _ _).injective.eq_iff

/-- The pullback along a morphism with a section is faithful: `δ^* q^* ≅ (δ ≫ q)^* = 𝟙^* ≅ 𝟭`. -/
lemma faithful_upperStar_of_comp_eq_id {V P : Scheme.{u}} (q : P ⟶ V) (δ : V ⟶ P)
    (hδ : δ ≫ q = 𝟙 V) : (q)^*⟦Λ⟧.Faithful :=
  Functor.Faithful.of_comp_iso
    ((upperStarComp Λ δ q).symm ≪≫ upperStarCongr Λ hδ ≪≫ upperStarId Λ V)

section KernelDescent

variable {S : Scheme.{u}} {ι : Type u} [Finite ι] {V : ι → Scheme.{u}} (f : ∀ k, V k ⟶ S)
  (M : Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
  {Q : ∀ k, Mod (Sheaf (ProEt.topology (V k)) Ab.{u + 1}) (condensedRingObj Λ (V k))}
  (π : ∀ k, (f k)^*⟦Λ⟧.obj M ⟶ Q k) {P : ι → ι → Scheme.{u}} {p₁ : ∀ j k, P j k ⟶ V j}
  {p₂ : ∀ j k, P j k ⟶ V k} (hP : ∀ j k, IsPullback (p₁ j k) (p₂ j k) (f j) (f k))
  (ψ : ∀ j k, (p₁ j k)^*⟦Λ⟧.obj (Q j) ≅ (p₂ j k)^*⟦Λ⟧.obj (Q k))

/-- The morphism `M ⟶ ∏_k f_{k*} Q_k` whose components are the adjoints of the
`π_k : f_k^* M ⟶ Q_k`. Its kernel is the descended subobject of
`ProEtale.CondensedRing.exists_iso_upperStar_kernel_kernelDescentMap`. -/
noncomputable def kernelDescentMap : M ⟶ ∏ᶜ fun k ↦ (f k)_*⟦Λ⟧.obj (Q k) :=
  Pi.lift fun k ↦ (upperStarLowerStarAdjunction Λ (f k)).unit.app M ≫ (f k)_*⟦Λ⟧.map (π k)

variable {Λ f M π ψ} in
/-- A component of `comp_upperStar_map_kernelDescentMap_eq_zero_iff`. -/
lemma comp_upperStar_map_kernelDescentMap_π_eq_zero_iff [∀ k, WeaklyEtale (f k)]
    (hψ : ∀ j k, (p₁ j k)^*⟦Λ⟧.map (π j) ≫ (ψ j k).hom =
      (upperStarSquareComparison Λ (hP j k).flip.toCommSq).hom.app M ≫
        (p₂ j k)^*⟦Λ⟧.map (π k)) (j k : ι)
    {T : Mod (Sheaf (ProEt.topology (V j)) Ab.{u + 1}) (condensedRingObj Λ (V j))}
    (v : T ⟶ (f j)^*⟦Λ⟧.obj M) :
    v ≫ (f j)^*⟦Λ⟧.map (kernelDescentMap Λ f M π) ≫ (f j)^*⟦Λ⟧.map (Pi.π _ k) = 0 ↔
      (p₁ j k)^*⟦Λ⟧.map (v ≫ π j) = 0 := by
  have e₁ : v ≫ (f j)^*⟦Λ⟧.map (kernelDescentMap Λ f M π) ≫ (f j)^*⟦Λ⟧.map (Pi.π _ k) =
      v ≫ (f j)^*⟦Λ⟧.map ((upperStarLowerStarAdjunction Λ (f k)).unit.app M ≫
        (f k)_*⟦Λ⟧.map (π k)) := by
    rw [← Functor.map_comp, kernelDescentMap, Pi.lift_comp_π]
  have e₂ : (p₁ j k)^*⟦Λ⟧.map (v ≫ π j) ≫ (ψ j k).hom =
      (p₁ j k)^*⟦Λ⟧.map v ≫ (upperStarSquareComparison Λ (hP j k).flip.toCommSq).hom.app M ≫
        (p₂ j k)^*⟦Λ⟧.map (π k) := by
    rw [Functor.map_comp, Category.assoc, hψ j k]
  rw [e₁, comp_upperStar_map_unit_eq_zero_iff Λ (hP j k), ← e₂]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, zero_comp]⟩
  rw [← Category.comp_id ((p₁ j k)^*⟦Λ⟧.map (v ≫ π j)), ← (ψ j k).hom_inv_id,
    ← Category.assoc, h, zero_comp]

variable {Λ f M π ψ} in
/-- Under the compatibility `hψ`, a morphism into `f_j^* M` kills the pullback of
`kernelDescentMap` if and only if it kills `π_j`. -/
lemma comp_upperStar_map_kernelDescentMap_eq_zero_iff [∀ k, WeaklyEtale (f k)]
    (hψ : ∀ j k, (p₁ j k)^*⟦Λ⟧.map (π j) ≫ (ψ j k).hom =
      (upperStarSquareComparison Λ (hP j k).flip.toCommSq).hom.app M ≫
        (p₂ j k)^*⟦Λ⟧.map (π k)) (j : ι)
    {T : Mod (Sheaf (ProEt.topology (V j)) Ab.{u + 1}) (condensedRingObj Λ (V j))}
    (v : T ⟶ (f j)^*⟦Λ⟧.obj M) :
    v ≫ (f j)^*⟦Λ⟧.map (kernelDescentMap Λ f M π) = 0 ↔ v ≫ π j = 0 := by
  have hk (k : ι) := comp_upperStar_map_kernelDescentMap_π_eq_zero_iff hP hψ j k v
  constructor
  · intro h
    have := faithful_upperStar_of_comp_eq_id Λ (p₁ j j)
      ((hP j j).lift (𝟙 _) (𝟙 _) rfl) ((hP j j).lift_fst _ _ _)
    rw [← Functor.map_eq_zero_iff (p₁ j j)^*⟦Λ⟧, ← hk j, reassoc_of% h, zero_comp]
  · intro h
    rw [← cancel_mono (piComparison (f j)^*⟦Λ⟧ fun k ↦ (f k)_*⟦Λ⟧.obj (Q k)), zero_comp]
    refine Pi.hom_ext _ _ fun k ↦ ?_
    rw [Category.assoc, Category.assoc, piComparison_comp_π, zero_comp, hk k, h,
      Functor.map_zero]

variable {Λ f M π ψ} in
/-- **Descent of compatible subobjects as a kernel.** Let `f_k : V_k ⟶ S` be a finite family of
weakly étale morphisms and `π_k : f_k^* M ⟶ Q_k` morphisms whose pullbacks to the fibre products
`V_j ×_S V_k` agree up to the isomorphisms `ψ`. Then the pullback along `f_j` of the kernel `K`
of `M ⟶ ∏_k f_{k*} Q_k` is the kernel of `π_j`: if `σ : F ⟶ f_j^* M` is a kernel of `π_j`, then
`F ≅ f_j^* K` compatibly with the inclusions into `f_j^* M`. -/
theorem exists_iso_upperStar_kernel_kernelDescentMap [∀ k, WeaklyEtale (f k)]
    (hψ : ∀ j k, (p₁ j k)^*⟦Λ⟧.map (π j) ≫ (ψ j k).hom =
      (upperStarSquareComparison Λ (hP j k).flip.toCommSq).hom.app M ≫
        (p₂ j k)^*⟦Λ⟧.map (π k)) (j : ι)
    {F : Mod (Sheaf (ProEt.topology (V j)) Ab.{u + 1}) (condensedRingObj Λ (V j))}
    (σ : F ⟶ (f j)^*⟦Λ⟧.obj M) (hσ : σ ≫ π j = 0) (hl : IsLimit (KernelFork.ofι σ hσ)) :
    ∃ e : F ≅ (f j)^*⟦Λ⟧.obj (kernel (kernelDescentMap Λ f M π)),
      e.hom ≫ (f j)^*⟦Λ⟧.map (kernel.ι (kernelDescentMap Λ f M π)) = σ := by
  let hK := KernelFork.mapIsLimit _ (kernelIsKernel (kernelDescentMap Λ f M π)) (f j)^*⟦Λ⟧
  have hmK : Mono ((f j)^*⟦Λ⟧.map (kernel.ι (kernelDescentMap Λ f M π))) :=
    Fork.IsLimit.mono hK
  have hmσ : Mono σ := Fork.IsLimit.mono hl
  obtain ⟨a, ha⟩ := KernelFork.IsLimit.lift' hK σ
    ((comp_upperStar_map_kernelDescentMap_eq_zero_iff hP hψ j σ).2 hσ)
  have hι : (f j)^*⟦Λ⟧.map (kernel.ι (kernelDescentMap Λ f M π)) ≫ π j = 0 :=
    (comp_upperStar_map_kernelDescentMap_eq_zero_iff hP hψ j _).1 (by
      rw [← Functor.map_comp, kernel.condition, Functor.map_zero])
  obtain ⟨b, hb⟩ := KernelFork.IsLimit.lift' hl _ hι
  replace ha : a ≫ (f j)^*⟦Λ⟧.map (kernel.ι (kernelDescentMap Λ f M π)) = σ := ha
  replace hb : b ≫ σ = (f j)^*⟦Λ⟧.map (kernel.ι (kernelDescentMap Λ f M π)) := hb
  refine ⟨⟨a, b, ?_, ?_⟩, ha⟩
  · rw [← cancel_mono σ, Category.assoc, hb, ha, Category.id_comp]
  · rw [← cancel_mono ((f j)^*⟦Λ⟧.map (kernel.ι (kernelDescentMap Λ f M π))), Category.assoc,
      ha, hb, Category.id_comp]

end KernelDescent

end AlgebraicGeometry.ProEtale.CondensedRing
