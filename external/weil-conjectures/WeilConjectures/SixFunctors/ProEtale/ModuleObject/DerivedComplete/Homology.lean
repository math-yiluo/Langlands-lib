/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.Basic
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimitMilnor
public import WeilConjectures.Algebra.Homology.DerivedCategory.SingleHomology
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.CategoryTheory.ModuleObjects.SequentialLimitEpi
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.CenterComplete

/-!
# Cohomology sheaves of derived complete complexes

Let `C` be an abelian category with exact countable products and K-injective resolutions, and
`z` an element of the center of `C`, inducing an element of the center of `D(C)`. For an object
`A` of `C`, the limit and the first derived limit of the tower `⋯ --z--> A --z--> A` are the
kernel and the cokernel of `1 - t` on `∏ₙ A`, where `t` is the shift `(aₙ)ₙ ↦ (z aₙ₊₁)ₙ`
(`CategoryTheory.CatCenter.powerShift`). The Milnor sequences
`0 ⟶ R¹lim Hᵠ⁻¹(K) ⟶ Hᵠ(R lim K) ⟶ lim Hᵠ(K) ⟶ 0` show that a complex `K` is `z`-complete,
i.e. the homotopy limit of `⋯ --z--> K --z--> K` vanishes, if and only if `1 - t` is invertible
on `∏ₙ Hᵠ(K)` for every `q` (`CategoryTheory.CatCenter.isCenterComplete_derivedCategory_iff`).
Applying this to `K` and to `Hᵠ(K)[0]` shows that `K` is complete if and only if all its
cohomology objects are (Stacks 09B9).

For `𝒪_{E,X}`-module objects on `X_proét` and the action of a uniformizer `ϖ` of `𝒪_E`, this
yields (Bhatt–Scholze, *The pro-étale topology for schemes*, Proposition 3.4.4; blueprint
`definition-derived-adic-completeness`):

## Main results

- `ProEtale.derivedCompleteIntegers_singleFunctor_homology`: the cohomology sheaves of a derived
  complete complex are derived complete; conversely
  `ProEtale.derivedCompleteIntegers_iff_forall_singleFunctor_homology`.
- `ProEtale.isZero_of_derivedCompleteIntegers_singleFunctor_of_epi`: **Nakayama's lemma** for
  derived complete sheaves: if `ϖ` acts surjectively on a derived complete sheaf `M`, then
  `M = 0`, as `lim (⋯ --ϖ--> M --ϖ--> M) = 0` surjects onto `M` by repleteness.
- `ProEtale.derivedCompleteIntegers_singleFunctor_kernel`,
  `ProEtale.derivedCompleteIntegers_singleFunctor_cokernel`: derived complete sheaves are closed
  under kernels and cokernels.
-/

@[expose] public section

open CategoryTheory Category Limits Opposite Pretriangulated

namespace CategoryTheory.CatCenter

variable {C : Type*} [Category* C] [Abelian C] (z : CatCenter C)

/-- The map induced on homology by the degreewise action of a central element `z` is the action
of `z` on the homology. -/
lemma homologyMap_mapHomologicalComplex_app {ι : Type*} (c : ComplexShape ι)
    (K : HomologicalComplex C c) (i : ι) :
    HomologicalComplex.homologyMap ((z.mapHomologicalComplex c).app K) i =
      z.app (K.homology i) := by
  have h : HomologicalComplex.cyclesMap ((z.mapHomologicalComplex c).app K) i =
      z.app (K.cycles i) := by
    rw [← cancel_mono (K.iCycles i), HomologicalComplex.cyclesMap_i,
      mapHomologicalComplex_app_f]
    exact z.naturality _
  rw [← cancel_epi (K.homologyπ i), HomologicalComplex.homologyπ_naturality, h]
  exact (z.naturality _).symm

variable [HasDerivedCategory C]

/-- The cohomology functors send the central element of `D(C)` induced by `z` to `z`. -/
lemma homologyFunctor_map_derivedCategory_app (q : ℤ) (K : DerivedCategory C) :
    (DerivedCategory.homologyFunctor C q).map (z.derivedCategory.app K) =
      z.app ((DerivedCategory.homologyFunctor C q).obj K) := by
  refine map_app_of_iso _ _ _ (DerivedCategory.Q.objObjPreimageIso K) ?_
  rw [derivedCategory_app_Q_obj]
  have h := (DerivedCategory.homologyFunctorFactors C q).hom.naturality
    ((z.mapHomologicalComplex (ComplexShape.up ℤ)).app (DerivedCategory.Q.objPreimage K))
  dsimp at h
  rw [← cancel_mono ((DerivedCategory.homologyFunctorFactors C q).hom.app _), h,
    HomologicalComplex.homologyFunctor_map, homologyMap_mapHomologicalComplex_app]
  exact z.naturality _

end CatCenter

end CategoryTheory

namespace CategoryTheory.Limits

/-- The limit of a tower `F` vanishes if and only if `1 - t` is a monomorphism, where
`t : ∏ Fₙ ⟶ ∏ Fₙ` has components `∏ Fₙ ⟶ Fₙ₊₁ ⟶ Fₙ`: the limit is the kernel of `1 - t`. -/
lemma Fan.IsLimit.isZero_iff_mono_one_sub {C : Type*} [Category* C] [Preadditive C]
    {F : ℕᵒᵖ ⥤ C} {P : Fan fun n : ℕ ↦ F.obj (Opposite.op n)} (hP : IsLimit P) (t : P.pt ⟶ P.pt)
    (ht : ∀ n : ℕ, t ≫ P.proj n = P.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op)
    {c : Cone F} (hc : IsLimit c) : IsZero c.pt ↔ Mono (𝟙 P.pt - t) := by
  let hk := Fan.IsLimit.isLimitKernelForkOneSub hP t ht hc
  refine ⟨fun h ↦ Preadditive.mono_of_cancel_zero _ fun g hg ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hk g hg
    rw [← hl, h.eq_of_tgt l 0, zero_comp]
  · have hι : Mono (Fan.IsLimit.lift hP fun n ↦ c.π.app (Opposite.op n)) := mono_of_isLimit_fork hk
    rw [IsZero.iff_id_eq_zero, ← cancel_mono (Fan.IsLimit.lift hP fun n ↦ c.π.app (Opposite.op n)),
      ← cancel_mono (𝟙 P.pt - t), zero_comp, zero_comp, id_comp]
    exact Fan.IsLimit.lift_π_comp_one_sub_eq_zero hP t ht c

end CategoryTheory.Limits

namespace CategoryTheory.CatCenter

open Pretriangulated

section PowerShift

variable {C : Type*} [Category* C] [HasLimitsOfShape (Discrete ℕ) C] (z : CatCenter C)

/-- The endomorphism `(aₙ)ₙ ↦ (z aₙ₊₁)ₙ` of the countable power `∏ₙ A`, for an element `z` of
the center: the transition endomorphism of the tower `⋯ --z--> A --z--> A`. The limit and the
first derived limit of this tower are the kernel and the cokernel of `1 - z.powerShift A`. -/
noncomputable def powerShift (A : C) :
    ∏ᶜ (fun _ : ℕ ↦ A) ⟶ ∏ᶜ (fun _ : ℕ ↦ A) :=
  Pi.lift fun n ↦ Pi.π _ (n + 1) ≫ z.app A

@[reassoc (attr := simp)]
lemma powerShift_π (A : C) (n : ℕ) :
    z.powerShift A ≫ Pi.π _ n = Pi.π _ (n + 1) ≫ z.app A :=
  Pi.lift_comp_π _ _

variable [Preadditive C]

/-- The endomorphisms `1 - z.powerShift A` are natural in `A`. -/
lemma map_comp_one_sub_powerShift {A B : C} (f : A ⟶ B) :
    Limits.Pi.map (fun _ ↦ f) ≫ (𝟙 _ - z.powerShift B) =
      (𝟙 _ - z.powerShift A) ≫ Limits.Pi.map fun _ ↦ f := by
  refine Pi.hom_ext _ _ fun n ↦ ?_
  simp only [Preadditive.comp_sub, Preadditive.sub_comp, comp_id, id_comp, assoc, powerShift_π,
    powerShift_π_assoc, Pi.map_π, Pi.map_π_assoc]
  rw [z.naturality]

/-- The invertibility of `1 - z.powerShift A`, i.e. the vanishing of the limit and of the first
derived limit of `⋯ --z--> A --z--> A`, is invariant under isomorphisms. -/
lemma isIso_one_sub_powerShift_of_iso {A B : C}
    (e : A ≅ B) [IsIso (𝟙 _ - z.powerShift A)] :
    IsIso (𝟙 _ - z.powerShift B) := by
  have h : 𝟙 _ - z.powerShift B =
      (Pi.mapIso fun _ ↦ e).inv ≫ (𝟙 _ - z.powerShift A) ≫ (Pi.mapIso fun _ ↦ e).hom := by
    rw [← (Pi.mapIso fun _ ↦ e).inv_hom_id_assoc (𝟙 _ - z.powerShift B)]
    exact congrArg _ (map_comp_one_sub_powerShift z e.hom)
  rw [h]
  infer_instance

/-- For a zero object `A`, the endomorphism `1 - z.powerShift A` is invertible. -/
lemma isIso_one_sub_powerShift_of_isZero {A : C} (hA : IsZero A) :
    IsIso (𝟙 _ - z.powerShift A) := by
  have h : IsZero (∏ᶜ fun _ : ℕ ↦ A) :=
    (IsZero.iff_id_eq_zero _).2 (Pi.hom_ext _ _ fun _ ↦ hA.eq_of_tgt _ _)
  exact ⟨0, h.eq_of_src _ _, h.eq_of_src _ _⟩

end PowerShift

section Derived

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [Abelian.HasKInjectiveResolutions C] [HasLimitsOfShape (Discrete ℕ) C]
  [HasExactLimitsOfShape (Discrete ℕ) C] [HasLimitsOfShape ℕᵒᵖ C] (z : CatCenter C)

open _root_.DerivedCategory

omit [Abelian.HasKInjectiveResolutions C] [HasExactLimitsOfShape (Discrete ℕ) C]
  [HasLimitsOfShape ℕᵒᵖ C] in
/-- The cohomology of the tower `⋯ --z--> L --z--> L` in `D(C)` is the tower
`⋯ --z--> Hᵠ(L) --z--> Hᵠ(L)`. -/
lemma powerShift_π_homologyFunctor_map (L : DerivedCategory C) (q : ℤ) (n : ℕ) :
    z.powerShift ((homologyFunctor C q).obj L) ≫ Pi.π _ n =
      Pi.π _ (n + 1) ≫
        (homologyFunctor C q).map
          ((centerTower z.derivedCategory L).map (homOfLE n.le_succ).op) := by
  rw [powerShift_π, centerTower_map_succ]
  exact congrArg _ (homologyFunctor_map_derivedCategory_app z q L).symm

/-- **The homotopy limit of `⋯ --z--> L --z--> L` vanishes if and only if, for every `q`, the
limit and the first derived limit of `⋯ --z--> Hᵠ(L) --z--> Hᵠ(L)` vanish**, by the Milnor
sequences `0 ⟶ R¹lim Hᵠ⁻¹(L) ⟶ Hᵠ(R lim L) ⟶ lim Hᵠ(L) ⟶ 0`. -/
theorem isZero_iff_of_isHomotopyLimit_centerTower {L : DerivedCategory C}
    {c : Cone (centerTower z.derivedCategory L)} (hc : IsHomotopyLimit c) :
    IsZero c.pt ↔ ∀ q : ℤ, IsIso (𝟙 _ - z.powerShift ((homologyFunctor C q).obj L)) := by
  have hlim (q : ℤ) : IsZero (limit (centerTower z.derivedCategory L ⋙ homologyFunctor C q)) ↔
      Mono (𝟙 _ - z.powerShift ((homologyFunctor C q).obj L)) :=
    Fan.IsLimit.isZero_iff_mono_one_sub (productIsProduct _) _
      (powerShift_π_homologyFunctor_map z L q) (limit.isLimit _)
  have hM (i j : ℤ) (hij : i + 1 = j) :
      ∃ (a : cokernel (𝟙 _ - z.powerShift ((homologyFunctor C i).obj L)) ⟶
      (homologyFunctor C j).obj c.pt)
      (hz : a ≫ (limit.isLimit _).lift ((homologyFunctor C j).mapCone c) = 0),
      (ShortComplex.mk _ _ hz).ShortExact := shortExact_milnor_of_isHomotopyLimit hc i j hij
    (productIsProduct _) _ (powerShift_π_homologyFunctor_map z L i) (limit.isLimit _)
  refine ⟨fun h q ↦ ?_, fun h ↦ isZero_of_forall_isZero_homology _ fun q ↦ ?_⟩
  · obtain ⟨a, hz, hS⟩ := hM q (q + 1) rfl
    obtain ⟨a', hz', hS'⟩ := hM (q - 1) q (by lia)
    have := hS.mono_f
    have := hS'.epi_g
    have : Epi (𝟙 _ - z.powerShift ((homologyFunctor C q).obj L)) :=
      Preadditive.epi_of_isZero_cokernel _
        (IsZero.of_mono a ((homologyFunctor C (q + 1)).map_isZero h))
    have : Mono (𝟙 _ - z.powerShift ((homologyFunctor C q).obj L)) :=
      (hlim q).1 (IsZero.of_epi ((limit.isLimit _).lift ((homologyFunctor C q).mapCone c))
        ((homologyFunctor C q).map_isZero h))
    exact isIso_of_mono_of_epi _
  · obtain ⟨a, hz, hS⟩ := hM (q - 1) q (by lia)
    exact hS.exact.isZero_X₂ ((isZero_cokernel_of_epi _).eq_of_src _ _)
      (((hlim q).2 inferInstance).eq_of_tgt _ _)

/-- A complex `K` is complete with respect to the central element of `D(C)` induced by `z` if and
only if, for every `q`, the limit and the first derived limit of `⋯ --z--> Hᵠ(K) --z--> Hᵠ(K)`
vanish. -/
theorem isCenterComplete_derivedCategory_iff (K : DerivedCategory C) :
    IsCenterComplete z.derivedCategory K ↔
      ∀ q : ℤ, IsIso (𝟙 _ - z.powerShift ((homologyFunctor C q).obj K)) := by
  obtain ⟨c, hc⟩ := exists_isHomotopyLimit (centerTower z.derivedCategory K)
  rw [← isZero_iff_of_isHomotopyLimit_centerTower z hc]
  exact ⟨fun hK ↦ hK.isZero_of_isHomotopyLimit (fun X ↦ z.derivedCategory_app_shift X 1) hc,
    isCenterComplete_of_isHomotopyLimit_centerTower hc⟩

/-- An object `A` placed in degree `0` is complete with respect to the central element of `D(C)`
induced by `z` if and only if the limit and the first derived limit of `⋯ --z--> A --z--> A`
vanish. -/
theorem isCenterComplete_derivedCategory_singleFunctor_iff (A : C) :
    IsCenterComplete z.derivedCategory ((singleFunctor C 0).obj A) ↔
      IsIso (𝟙 _ - z.powerShift A) := by
  rw [isCenterComplete_derivedCategory_iff]
  refine ⟨fun h ↦ ?_, fun h q ↦ ?_⟩
  · have := h 0
    exact isIso_one_sub_powerShift_of_iso z
      (A := (homologyFunctor C 0).obj ((singleFunctor C 0).obj A))
      (B := A) ((singleFunctorCompHomologyFunctorIso C 0).app A)
  · by_cases hq : q = 0
    · subst hq
      exact isIso_one_sub_powerShift_of_iso z (A := A)
        (B := (homologyFunctor C 0).obj ((singleFunctor C 0).obj A))
        ((singleFunctorCompHomologyFunctorIso C 0).app A).symm
    · exact isIso_one_sub_powerShift_of_isZero z
        (isZero_homologyFunctor_obj_of_iso_singleFunctor (Iso.refl _) hq)

/-- **The cohomology objects of a complete complex are complete** (Stacks 09B9): if `K` is
complete with respect to the central element of `D(C)` induced by `z`, so is `Hᵠ(K)` placed in
degree `0`. -/
theorem isCenterComplete_derivedCategory_singleFunctor_homologyFunctor_obj
    {K : DerivedCategory C} (hK : IsCenterComplete z.derivedCategory K) (q : ℤ) :
    IsCenterComplete z.derivedCategory ((singleFunctor C 0).obj ((homologyFunctor C q).obj K)) := by
  rw [isCenterComplete_derivedCategory_iff] at hK
  have := hK q
  rwa [isCenterComplete_derivedCategory_singleFunctor_iff]

/-- A complex is complete with respect to the central element of `D(C)` induced by `z` if and
only if all its cohomology objects are. -/
theorem isCenterComplete_derivedCategory_iff_forall_singleFunctor_homologyFunctor_obj
    (K : DerivedCategory C) :
    IsCenterComplete z.derivedCategory K ↔ ∀ q : ℤ,
      IsCenterComplete z.derivedCategory
        ((singleFunctor C 0).obj ((homologyFunctor C q).obj K)) := by
  simp only [isCenterComplete_derivedCategory_iff z K,
    isCenterComplete_derivedCategory_singleFunctor_iff]

/-- **Nakayama's lemma for complete objects**: if an object `A` placed in degree `0` is complete
with respect to the central element of `D(C)` induced by `z` and `z` acts surjectively on `A`,
then `A = 0`, provided the projection `lim Aₙ ⟶ A₀` of a tower of epimorphisms of `C` is an
epimorphism. Indeed the limit of `⋯ --z--> A --z--> A` vanishes, and projects onto `A`. -/
theorem isZero_of_isCenterComplete_singleFunctor_of_epi (hC : EpiπAppZeroOfEpi C) {A : C}
    (hA : IsCenterComplete z.derivedCategory ((singleFunctor C 0).obj A)) [Epi (z.app A)] :
    IsZero A := by
  rw [isCenterComplete_derivedCategory_singleFunctor_iff] at hA
  have h₀ : IsZero (limit (centerTower z A)) :=
    (Fan.IsLimit.isZero_iff_mono_one_sub (F := centerTower z A)
      (P := Fan.mk (∏ᶜ fun _ : ℕ ↦ A) (Pi.π _)) (productIsProduct fun _ : ℕ ↦ A) (z.powerShift A)
      (fun n ↦ (powerShift_π z A n).trans (congrArg _ (centerTower_map_succ z A n).symm))
      (limit.isLimit _)).2 (inferInstance : Mono (𝟙 (∏ᶜ fun _ : ℕ ↦ A) - z.powerShift A))
  have := hC (limit.isLimit (centerTower z A)) fun n ↦ by
    rw [centerTower_map_succ]
    infer_instance
  exact IsZero.of_epi ((limit.cone (centerTower z A)).π.app (op 0)) h₀

/-- **Kernels of morphisms between complete objects are complete**: if `X` and `Y` placed in
degree `0` are complete with respect to the central element of `D(C)` induced by `z`, then so is
the kernel of any `f : X ⟶ Y`. It is `H⁻¹` of the cone of `f`, which is complete. -/
theorem isCenterComplete_derivedCategory_singleFunctor_kernel {X Y : C} (f : X ⟶ Y)
    (hX : IsCenterComplete z.derivedCategory ((singleFunctor C 0).obj X))
    (hY : IsCenterComplete z.derivedCategory ((singleFunctor C 0).obj Y)) :
    IsCenterComplete z.derivedCategory ((singleFunctor C 0).obj (kernel f)) := by
  obtain ⟨Z, g, δ, hT⟩ := distinguished_cocone_triangle ((singleFunctor C 0).map f)
  have hZ : IsCenterComplete z.derivedCategory Z :=
    hY.ext₂ _ (rot_of_distTriang _ hT) (hX.shift z.derivedCategory_app_shift 1)
  let e := singleFunctorCompHomologyFunctorIso C 0
  have hn : e.hom.app X ≫ f = (homologyFunctor C 0).map ((singleFunctor C 0).map f) ≫ e.hom.app Y :=
    (e.hom.naturality f).symm
  have : Mono (HomologySequence.δ (Triangle.mk ((singleFunctor C 0).map f) g δ) (-1) 0) :=
    (HomologySequence.exact₃ _ hT (-1) 0).mono_g
      ((isZero_homologyFunctor_obj_of_iso_singleFunctor (Iso.refl _) (by lia)).eq_of_src _ _)
  let S := ShortComplex.mk
    (HomologySequence.δ (Triangle.mk ((singleFunctor C 0).map f) g δ) (-1) 0 ≫ e.hom.app X) f
    (by
      rw [assoc, hn]
      exact (HomologySequence.δ_comp_assoc _ hT (-1) 0 _ _).trans zero_comp)
  have hS : S.Exact := by
    refine ShortComplex.exact_of_iso ?_ (HomologySequence.exact₁ _ hT (-1) 0)
    exact ShortComplex.isoMk (Iso.refl _) (e.app X) (e.app Y) (by simp [S]) hn
  have : Mono S.f := mono_comp _ _
  have i := hS.fIsKernel.conePointUniqueUpToIso (kernelIsKernel f)
  exact (isCenterComplete_derivedCategory_singleFunctor_homologyFunctor_obj z hZ (-1)).of_iso
    ((singleFunctor C 0).mapIso i)

/-- **Cokernels of morphisms between complete objects are complete**: if `X` and `Y` placed in
degree `0` are complete with respect to the central element of `D(C)` induced by `z`, then so is
the cokernel of any `f : X ⟶ Y`. It is `H⁰` of the cone of `f`, which is complete. -/
theorem isCenterComplete_derivedCategory_singleFunctor_cokernel {X Y : C} (f : X ⟶ Y)
    (hX : IsCenterComplete z.derivedCategory ((singleFunctor C 0).obj X))
    (hY : IsCenterComplete z.derivedCategory ((singleFunctor C 0).obj Y)) :
    IsCenterComplete z.derivedCategory ((singleFunctor C 0).obj (cokernel f)) := by
  obtain ⟨Z, g, δ, hT⟩ := distinguished_cocone_triangle ((singleFunctor C 0).map f)
  have hZ : IsCenterComplete z.derivedCategory Z :=
    hY.ext₂ _ (rot_of_distTriang _ hT) (hX.shift z.derivedCategory_app_shift 1)
  let e := singleFunctorCompHomologyFunctorIso C 0
  have hn : f ≫ e.inv.app Y = e.inv.app X ≫ (homologyFunctor C 0).map ((singleFunctor C 0).map f) :=
    e.inv.naturality f
  have : Epi ((homologyFunctor C 0).map g) :=
    (HomologySequence.exact₃ (Triangle.mk ((singleFunctor C 0).map f) g δ) hT 0 1).epi_f
      ((isZero_homologyFunctor_obj_of_iso_singleFunctor (Iso.refl _) (by lia)).eq_of_tgt _ _)
  let S := ShortComplex.mk f (e.inv.app Y ≫ (homologyFunctor C 0).map g)
    (by
      have h₀ : (singleFunctor C 0).map f ≫ g = 0 := comp_distTriang_mor_zero₁₂ _ hT
      rw [reassoc_of% hn, ← Functor.map_comp, h₀, Functor.map_zero, comp_zero])
  have hS : S.Exact := by
    refine ShortComplex.exact_of_iso ?_ (HomologySequence.exact₂ _ hT 0)
    exact ShortComplex.isoMk (e.app X) (e.app Y) (Iso.refl _) (e.hom.naturality f).symm
      (by simp [S])
  have : Epi S.g := epi_comp _ _
  exact (isCenterComplete_derivedCategory_singleFunctor_homologyFunctor_obj z hZ 0).of_iso
    ((singleFunctor C 0).mapIso
      ((cokernelIsCokernel f).coconePointUniqueUpToIso hS.gIsCokernel).symm)

end Derived

end CategoryTheory.CatCenter

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

open scoped CategoryTheory.Obj CategoryTheory.Functor ZeroObject

universe u

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : Type} [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] {X : Scheme.{u}}

/-- **The cohomology sheaves of a derived complete complex are derived complete**
(Bhatt–Scholze, Proposition 3.4.4; Stacks 09B9): if `K` is derived complete, so is `Hᵠ(K)`
placed in degree `0`. -/
theorem derivedCompleteIntegers_singleFunctor_homology
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))}
    (hK : derivedCompleteIntegers ℓ E X K) (q : ℤ) :
    derivedCompleteIntegers ℓ E X
      ((DerivedCategory.singleFunctor _ 0).obj ((DerivedCategory.homologyFunctor _ q).obj K)) := by
  obtain ⟨ϖ, hϖ⟩ := PadicAlgCl.isPrincipal_maximalIdeal_integers ℓ E
  rw [Ideal.submodule_span_eq] at hϖ
  rw [derivedCompleteIntegers_iff_isCenterComplete hϖ] at hK ⊢
  exact CatCenter.isCenterComplete_derivedCategory_singleFunctor_homologyFunctor_obj _ hK q

/-- A complex is derived complete if and only if all its cohomology sheaves are. -/
theorem derivedCompleteIntegers_iff_forall_singleFunctor_homology
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))) :
    derivedCompleteIntegers ℓ E X K ↔ ∀ q : ℤ, derivedCompleteIntegers ℓ E X
      ((DerivedCategory.singleFunctor _ 0).obj ((DerivedCategory.homologyFunctor _ q).obj K)) := by
  obtain ⟨ϖ, hϖ⟩ := PadicAlgCl.isPrincipal_maximalIdeal_integers ℓ E
  rw [Ideal.submodule_span_eq] at hϖ
  simp only [derivedCompleteIntegers_iff_isCenterComplete hϖ]
  exact CatCenter.isCenterComplete_derivedCategory_iff_forall_singleFunctor_homologyFunctor_obj _ K

omit [FiniteDimensional ℚ_[ℓ] E] in
/-- **Nakayama's lemma for derived complete sheaves**: a module object `M` which is derived
complete when placed in degree `0`, and on which a uniformizer `ϖ` of `𝒪_E` acts surjectively,
vanishes. Indeed `lim (⋯ --ϖ--> M --ϖ--> M)` vanishes, and surjects onto `M` by repleteness of
the pro-étale topos. -/
theorem isZero_of_derivedCompleteIntegers_singleFunctor_of_epi {ϖ : PadicAlgCl.integers ℓ E}
    (hϖ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E) = Ideal.span {ϖ})
    {M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)}
    (hM : derivedCompleteIntegers ℓ E X ((DerivedCategory.singleFunctor _ 0).obj M))
    [Epi ((padicIntegersCenter X ℓ E ϖ).app M)] : IsZero M := by
  rw [derivedCompleteIntegers_iff_isCenterComplete hϖ] at hM
  exact CatCenter.isZero_of_isCenterComplete_singleFunctor_of_epi _
    (Mod.epiπAppZeroOfEpi Scheme.ProEt.epi_π_app_zero_of_epi_addCommGrpCat) hM

/-- **Kernels of morphisms between derived complete sheaves are derived complete.** -/
theorem derivedCompleteIntegers_singleFunctor_kernel
    {M N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)} (f : M ⟶ N)
    (hM : derivedCompleteIntegers ℓ E X ((DerivedCategory.singleFunctor _ 0).obj M))
    (hN : derivedCompleteIntegers ℓ E X ((DerivedCategory.singleFunctor _ 0).obj N)) :
    derivedCompleteIntegers ℓ E X ((DerivedCategory.singleFunctor _ 0).obj (kernel f)) := by
  obtain ⟨ϖ, hϖ⟩ := PadicAlgCl.isPrincipal_maximalIdeal_integers ℓ E
  rw [Ideal.submodule_span_eq] at hϖ
  rw [derivedCompleteIntegers_iff_isCenterComplete hϖ] at hM hN ⊢
  exact CatCenter.isCenterComplete_derivedCategory_singleFunctor_kernel _ f hM hN

/-- **Cokernels of morphisms between derived complete sheaves are derived complete.** -/
theorem derivedCompleteIntegers_singleFunctor_cokernel
    {M N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)} (f : M ⟶ N)
    (hM : derivedCompleteIntegers ℓ E X ((DerivedCategory.singleFunctor _ 0).obj M))
    (hN : derivedCompleteIntegers ℓ E X ((DerivedCategory.singleFunctor _ 0).obj N)) :
    derivedCompleteIntegers ℓ E X ((DerivedCategory.singleFunctor _ 0).obj (cokernel f)) := by
  obtain ⟨ϖ, hϖ⟩ := PadicAlgCl.isPrincipal_maximalIdeal_integers ℓ E
  rw [Ideal.submodule_span_eq] at hϖ
  rw [derivedCompleteIntegers_iff_isCenterComplete hϖ] at hM hN ⊢
  exact CatCenter.isCenterComplete_derivedCategory_singleFunctor_cokernel _ f hM hN

end AlgebraicGeometry.ProEtale
