/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Adjunction.Triple
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.GeometricFrobenius
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Complement
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Mono

/-!
# Extension by zero of sheaves of modules over the constant sheaf

This is the counterpart, for a commutative coefficient ring `Λ` with an ultrametric norm (the
cases of interest being a finite extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ` and its ring of integers
`𝒪_E`), of
`WeilConjectures.SixFunctors.ProEtale.Adic.OpenImmersion`, which treats `ℚ̄_ℓ`,
with the same proofs; the constant sheaf `Λ_X : U ↦ C(U, Λ)` is that of
`WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ConstantSheaf`.

For an open immersion `j : U ⟶ X`, the pullback `j^*` of sheaves of `Λ_X`-modules
(`AlgebraicGeometry.ProEtale.fieldUpperStar`) preserves limits, its underlying functor being the
restriction along the localization functor. Hence it has a left adjoint, the extension by zero
`j_!` (`AlgebraicGeometry.ProEtale.fieldOpenImmersionLowerShriek`), by the special adjoint functor
theorem in the Grothendieck abelian category of sheaves of `Λ_X`-modules. The pushforward `j_*`
is fully faithful (the counit of `j^* ⊣ j_*` is invertible), hence so is `j_!`, and `j_! F`
vanishes along every morphism missing the range of `j`.

On underlying sheaves, `j_!` is the extension by zero of sheaves
(`AlgebraicGeometry.ProEtale.fieldOpenImmersionLowerShriekComparison`), hence exact. The point is
that the underlying sheaf of `j_! M` is an extension by zero, i.e. the counit of `j_! ⊣ j^*` on
sheaves is invertible there. For a free module `Λ_U ⊗ P` the underlying sheaf of `j_!` is
`Λ_X ⊗ j_! P`, the tensor product of a sheaf with a presheaf vanishing away from `U`,
sheafified; and every module is a cokernel of a morphism of free modules.

## Main definitions

- `AlgebraicGeometry.ProEtale.fieldOpenImmersionLowerShriek`: `j_!`, with notation `(j)_!ᶠ[Λ]`.
- `AlgebraicGeometry.ProEtale.fieldOpenImmersionLowerShriekComparison`: the comparison
  `j_! M.X ⟶ (j_! M).X`, an isomorphism, giving the exactness of `j_!`.
- `AlgebraicGeometry.ProEtale.fieldOpenImmersionLowerShriekToLowerStar`: the comparison
  `j_! ⟶ j_*`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

variable {Λ : Type} [NormedCommRing Λ] [IsUltrametricDist Λ]

omit [IsUltrametricDist Λ] in
/-- A sheaf of `Λ_X`-modules whose underlying sheaf vanishes is zero. -/
lemma FieldSheaf.isZero_of_isZero_X {X : Scheme.{u}} {M : FieldSheaf Λ X} (h : IsZero M.X) :
    IsZero M :=
  ⟨fun _ ↦ ⟨⟨0⟩, fun _ ↦ Mod.hom_ext _ _ (h.eq_of_src _ _)⟩,
    fun _ ↦ ⟨⟨0⟩, fun _ ↦ Mod.hom_ext _ _ (h.eq_of_tgt _ _)⟩⟩

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

instance : PreservesLimits ((j)^*[FieldCoefficients.{u} Λ]) :=
  preservesLimits_of_natIso (upperStarIsoOpenImmersionRestriction _ j).symm

instance (X : Scheme.{u}) : PreservesLimits (FieldSheaf.forget (Λ := Λ) X) where
  preservesLimitsOfShape := inferInstance

instance : PreservesLimits ((j)^*ᶠ[Λ]) := by
  have : PreservesLimits ((j)^*ᶠ[Λ] ⋙ FieldSheaf.forget U) :=
    inferInstanceAs (PreservesLimits (FieldSheaf.forget X ⋙ (j)^*[FieldCoefficients.{u} Λ]))
  exact preservesLimits_of_reflects_of_preserves _ (FieldSheaf.forget U)

instance : (j)^*ᶠ[Λ].IsRightAdjoint :=
  isRightAdjoint_of_preservesLimits_of_isCoseparating (D := FieldSheaf Λ X)
    (isCoseparator_coseparator (FieldSheaf Λ X)) (j)^*ᶠ[Λ]

variable (Λ) in
/-- The extension by zero `j_!` of sheaves of modules over the constant sheaves `Λ_X` along an
open immersion `j`: the left adjoint of the pullback `j^*`. -/
noncomputable def fieldOpenImmersionLowerShriek : FieldSheaf Λ U ⥤ FieldSheaf Λ X :=
  (j)^*ᶠ[Λ].leftAdjoint

@[inherit_doc fieldOpenImmersionLowerShriek]
scoped notation "(" j ")_!ᶠ[" Λ "]" => fieldOpenImmersionLowerShriek Λ j

variable (Λ) in
/-- The adjunction `j_! ⊣ j^*`. -/
noncomputable def fieldOpenImmersionLowerShriekAdjunction : (j)_!ᶠ[Λ] ⊣ (j)^*ᶠ[Λ] :=
  Adjunction.ofIsRightAdjoint _

instance : (j)_!ᶠ[Λ].IsLeftAdjoint :=
  (fieldOpenImmersionLowerShriekAdjunction Λ j).isLeftAdjoint

instance : (j)_!ᶠ[Λ].Additive :=
  (fieldOpenImmersionLowerShriekAdjunction Λ j).left_adjoint_additive

instance : IsIso (upperStarLowerStarAdjunction (FieldCoefficients.{u} Λ) j).counit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro N
  rw [← Adjunction.leftAdjointUniq_hom_app_counit (upperStarLowerStarAdjunction _ j)
    (openImmersionRestrictionLowerStarAdjunction _ j)]
  exact inferInstanceAs (IsIso ((upperStarIsoOpenImmersionRestriction _ j).hom.app _ ≫ _))

/-- The counit of `j^* ⊣ j_*` along an open immersion is invertible. -/
instance : IsIso (fieldUpperStarLowerStarAdjunction Λ j).counit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro N
  have : IsIso ((fieldUpperStarLowerStarAdjunction Λ j).counit.app N).hom := by
    rw [fieldUpperStarLowerStarAdjunction, Adjunction.modAdjunction_counit_app_hom]
    infer_instance
  have : IsIso ((FieldSheaf.forget U).map ((fieldUpperStarLowerStarAdjunction Λ j).counit.app N)) :=
    this
  exact isIso_of_reflects_iso _ (FieldSheaf.forget U)

/-- The unit of `j_! ⊣ j^*` along an open immersion is invertible: `j_!` is fully faithful, as
is `j_*`. -/
instance : IsIso (fieldOpenImmersionLowerShriekAdjunction Λ j).unit :=
  (Adjunction.Triple.isIso_unit_iff_isIso_counit
    ⟨fieldOpenImmersionLowerShriekAdjunction Λ j, fieldUpperStarLowerStarAdjunction Λ j⟩).2
    inferInstance

omit [IsUltrametricDist Λ] in
/-- The tensor product of a sheaf with an extension by zero is again an extension by zero: the
counit of `j_! ⊣ j^*` is invertible at `B ⊗ j_! P`. Before sheafification, `B ⊗ j_! P` is the
tensor product of `B` with a presheaf vanishing away from `U`. -/
lemma isIso_fieldOpenImmersionLowerShriek_counit_app_tensor
    {G : Sheaf (Scheme.ProEt.topology X) (FieldCoefficients.{u} Λ) ⥤
      Sheaf (Scheme.ProEt.topology U) (FieldCoefficients.{u} Λ)}
    (adj : (j)_!open[FieldCoefficients.{u} Λ] ⊣ G)
    (B : Sheaf (Scheme.ProEt.topology X) (FieldCoefficients.{u} Λ))
    (P : Sheaf (Scheme.ProEt.topology U) (FieldCoefficients.{u} Λ)) :
    IsIso (adj.counit.app (B ⊗ (j)_!open[FieldCoefficients.{u} Λ].obj P)) := by
  let L := (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).op
  let T := L.lan.obj P.obj
  have hR (W) (hW : IsEmpty (CostructuredArrow L W)) : IsZero ((B.obj ⊗ T).obj W) :=
    isZero_tensorObj_of_isZero_right _ (L.isInitialLanObjObj P.obj hW).isZero
  have e : B ⊗ (j)_!open[FieldCoefficients.{u} Λ].obj P ≅
      (presheafToSheaf (Scheme.ProEt.topology X) (FieldCoefficients.{u} Λ)).obj (B.obj ⊗ T) :=
    whiskerRightIso (asIso ((sheafificationAdjunction (Scheme.ProEt.topology X)
      (FieldCoefficients.{u} Λ)).counit.app B)).symm _ ≪≫
      Functor.Monoidal.μIso (presheafToSheaf (Scheme.ProEt.topology X)
        (FieldCoefficients.{u} Λ)) B.obj T
  exact adj.isIso_counit_app_of_iso
    (e ≪≫ presheafToSheafObjIsoOpenImmersionLowerShriek _ j _ hR)

/-- The counit of `j_! ⊣ j^*` on sheaves is invertible at the underlying sheaf of the extension by
zero `j_! M` of every sheaf of `Λ_U`-modules `M`. This holds for free modules, the extension by
zero of `Λ_U ⊗ P` being `Λ_X ⊗ j_! P`, and is inherited by cokernels, every module being a
cokernel of a morphism of free modules. -/
lemma isIso_fieldOpenImmersionLowerShriekUpperStarAdjunction_counit_app_forget
    (M : FieldSheaf Λ U) :
    IsIso ((openImmersionLowerShriekUpperStarAdjunction (FieldCoefficients.{u} Λ) j).counit.app
      ((FieldSheaf.forget X).obj ((j)_!ᶠ[Λ].obj M))) := by
  let adj := openImmersionLowerShriekUpperStarAdjunction (FieldCoefficients.{u} Λ) j
  let S : ObjectProperty (FieldSheaf Λ U) := fun M ↦
    IsIso (adj.counit.app ((FieldSheaf.forget X).obj ((j)_!ᶠ[Λ].obj M)))
  have hiso {M N : FieldSheaf Λ U} (e : M ≅ N) (hM : S M) : S N := by
    have : IsIso (adj.counit.app ((FieldSheaf.forget X).obj ((j)_!ᶠ[Λ].obj M))) := hM
    exact NatTrans.isIso_app_of_iso adj.counit
      ((FieldSheaf.forget X).mapIso ((j)_!ᶠ[Λ].mapIso e)).symm
  have hfree (P : Sheaf (Scheme.ProEt.topology U) (FieldCoefficients.{u} Λ)) :
      S ((Mod.free _).obj P) := by
    let e := Adjunction.leftAdjointUniq
      ((Mod.freeForgetAdjunction (fieldConstantSheaf Λ U)).comp
        (fieldOpenImmersionLowerShriekAdjunction Λ j))
      (adj.comp (Mod.freeForgetAdjunction (fieldConstantSheaf Λ X)))
    have : IsIso (adj.counit.app ((FieldSheaf.forget X).obj
        ((Mod.free (fieldConstantSheaf Λ X)).obj ((j)_!open[FieldCoefficients.{u} Λ].obj P)))) :=
      isIso_fieldOpenImmersionLowerShriek_counit_app_tensor j adj (fieldConstantSheaf Λ X) P
    exact @NatTrans.isIso_app_of_iso _ _ _ _ _ _ adj.counit _ _
      ((FieldSheaf.forget X).mapIso (e.app P)) this
  have hcoker {M N : FieldSheaf Λ U} (f : M ⟶ N) (hM : S M) (hN : S N) : S (cokernel f) := by
    have : IsIso (adj.counit.app ((FieldSheaf.forget X).obj ((j)_!ᶠ[Λ].obj M))) := hM
    have : IsIso (adj.counit.app ((FieldSheaf.forget X).obj ((j)_!ᶠ[Λ].obj N))) := hN
    have : IsIso (adj.counit.app (cokernel (((j)_!ᶠ[Λ] ⋙ FieldSheaf.forget X).map f))) :=
      adj.isIso_counit_app_cokernel ((FieldSheaf.forget X).map ((j)_!ᶠ[Λ].map f))
    exact NatTrans.isIso_app_of_iso adj.counit
      (PreservesCokernel.iso ((j)_!ᶠ[Λ] ⋙ FieldSheaf.forget X) f)
  -- every module is a cokernel of a morphism of free modules
  let ε := (Mod.freeForgetAdjunction (fieldConstantSheaf Λ U)).counit
  have hepi (N : FieldSheaf Λ U) : Epi (ε.app N) := by
    have : IsSplitEpi ((Mod.forget _).map (ε.app N)) :=
      ⟨⟨(λ_ N.X).inv ≫ MonObj.one ▷ N.X, Mod.unit_freeDesc _ (𝟙 N.X)⟩⟩
    exact (Mod.forget _).epi_of_epi_map inferInstance
  let p := ε.app M
  have e : M ≅ cokernel (ε.app (kernel p) ≫ kernel.ι p) :=
    (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel p)).coconePointUniqueUpToIso
      (colimit.isColimit _) ≪≫ (cokernelEpiComp _ _).symm
  exact hiso e.symm (hcoker _ (hfree _) (hfree _))

variable (Λ) in
/-- The comparison `j_! M.X ⟶ (j_! M).X` of the extension by zero of the underlying sheaf of a
sheaf of `Λ_U`-modules `M` with the underlying sheaf of its extension by zero. -/
noncomputable def fieldOpenImmersionLowerShriekComparison :
    FieldSheaf.forget U ⋙ (j)_!open[FieldCoefficients.{u} Λ] ⟶ (j)_!ᶠ[Λ] ⋙ FieldSheaf.forget X :=
  Functor.whiskerRight (Functor.whiskerRight (fieldOpenImmersionLowerShriekAdjunction Λ j).unit
      (FieldSheaf.forget U)) (j)_!open[FieldCoefficients.{u} Λ] ≫
    Functor.whiskerLeft ((j)_!ᶠ[Λ] ⋙ FieldSheaf.forget X)
      (openImmersionLowerShriekUpperStarAdjunction (FieldCoefficients.{u} Λ) j).counit

instance : IsIso (fieldOpenImmersionLowerShriekComparison Λ j) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have := isIso_fieldOpenImmersionLowerShriekUpperStarAdjunction_counit_app_forget j M
  dsimp [fieldOpenImmersionLowerShriekComparison]
  infer_instance

/-- **Extension by zero is exact.** On underlying sheaves it is the extension by zero of
sheaves, which is exact. -/
instance : PreservesFiniteLimits (j)_!ᶠ[Λ] := by
  have : PreservesFiniteLimits ((j)_!ᶠ[Λ] ⋙ FieldSheaf.forget X) :=
    preservesFiniteLimits_of_natIso (asIso (fieldOpenImmersionLowerShriekComparison Λ j))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (FieldSheaf.forget X)

/-- The pullback of `j_! F` along a morphism `g` missing the range of `j` vanishes: the
adjunctions turn `Hom(g^* j_! F, H)` into `Hom(F, j^* g_* H)`, and the underlying sheaf of
`j^* g_* H` vanishes. -/
lemma isZero_fieldUpperStar_fieldOpenImmersionLowerShriek {W : Scheme.{u}} (g : W ⟶ X)
    (hjg : Set.range j.base ∩ Set.range g.base = ∅) (F : FieldSheaf Λ U) :
    IsZero ((g)^*ᶠ[Λ].obj ((j)_!ᶠ[Λ].obj F)) := by
  have hz (H : FieldSheaf Λ W) : IsZero ((j)^*ᶠ[Λ].obj ((g)_*ᶠ[Λ].obj H)) :=
    FieldSheaf.isZero_of_isZero_X ((isZero_openImmersionRestriction_lowerStar _ g j
      (by rw [Set.inter_comm]; exact hjg) H.X).of_iso
        ((upperStarIsoOpenImmersionRestriction _ j).app _))
  refine (isZero_zero _).of_iso (IsInitial.uniqueUpToIso (IsInitial.ofUnique (h := fun H ↦ ?_))
    HasZeroObject.zeroIsInitial)
  haveI : Unique (F ⟶ (j)^*ᶠ[Λ].obj ((g)_*ᶠ[Λ].obj H)) :=
    ⟨⟨(hz H).isTerminal.from F⟩, fun _ ↦ (hz H).isTerminal.hom_ext _ _⟩
  exact Equiv.unique (((fieldUpperStarLowerStarAdjunction Λ g).homEquiv _ H).trans
    ((fieldOpenImmersionLowerShriekAdjunction Λ j).homEquiv F _))

variable (Λ) in
/-- The comparison `j_! ⟶ j_*` along an open immersion, from the adjoint triple
`j_! ⊣ j^* ⊣ j_*`: insert the inverse of the counit of `j^* ⊣ j_*` and contract with the counit
of `j_! ⊣ j^*`. -/
noncomputable def fieldOpenImmersionLowerShriekToLowerStar : (j)_!ᶠ[Λ] ⟶ (j)_*ᶠ[Λ] :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (inv (fieldUpperStarLowerStarAdjunction Λ j).counit) (j)_!ᶠ[Λ] ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (j)_*ᶠ[Λ] (fieldOpenImmersionLowerShriekAdjunction Λ j).counit ≫
    (Functor.rightUnitor _).hom

/-- The comparison `j_! ⟶ j_*` is characterised by its transpose under `j_! ⊣ j^*`: the inverse
of the counit of `j^* ⊣ j_*`. -/
lemma fieldOpenImmersionLowerShriekAdjunction_unit_app_comp_map_lowerShriekToLowerStar
    (F : FieldSheaf Λ U) :
    (fieldOpenImmersionLowerShriekAdjunction Λ j).unit.app F ≫
        (j)^*ᶠ[Λ].map ((fieldOpenImmersionLowerShriekToLowerStar Λ j).app F) =
      inv ((fieldUpperStarLowerStarAdjunction Λ j).counit.app F) := by
  simp only [fieldOpenImmersionLowerShriekToLowerStar, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.leftUnitor_inv_app,
    Functor.associator_hom_app, Functor.rightUnitor_hom_app, Category.id_comp, Functor.map_comp]
  erw [(fieldOpenImmersionLowerShriekAdjunction Λ j).unit_naturality_assoc,
    (fieldOpenImmersionLowerShriekAdjunction Λ j).right_triangle_components_assoc ((j)_*ᶠ[Λ].obj F),
    CategoryTheory.Functor.map_id, Category.comp_id]
  exact NatIso.isIso_inv_app _ _

/-- **The comparison `j_! M ⟶ j_* M` is a monomorphism.** Its kernel `K` restricts to zero on
`U`, `j^*` of the comparison being invertible, and its underlying sheaf is a subsheaf of the
extension by zero of the underlying sheaf of `M`; such a subsheaf vanishes
(`AlgebraicGeometry.ProEtale.isZero_of_mono_openImmersionLowerShriek`). -/
instance mono_fieldOpenImmersionLowerShriekToLowerStar_app (M : FieldSheaf Λ U) :
    Mono ((fieldOpenImmersionLowerShriekToLowerStar Λ j).app M) := by
  let c := (fieldOpenImmersionLowerShriekToLowerStar Λ j).app M
  have : IsIso ((j)^*ᶠ[Λ].map c) := by
    have : IsIso ((fieldOpenImmersionLowerShriekAdjunction Λ j).unit.app M ≫ (j)^*ᶠ[Λ].map c) := by
      rw [fieldOpenImmersionLowerShriekAdjunction_unit_app_comp_map_lowerShriekToLowerStar]
      infer_instance
    exact IsIso.of_isIso_comp_left ((fieldOpenImmersionLowerShriekAdjunction Λ j).unit.app M) _
  refine Preadditive.mono_of_isZero_kernel _ (FieldSheaf.isZero_of_isZero_X ?_)
  let i : (kernel c).X ⟶ (j)_!open[FieldCoefficients.{u} Λ].obj M.X :=
    (FieldSheaf.forget X).map (kernel.ι c) ≫
      inv ((fieldOpenImmersionLowerShriekComparison Λ j).app M)
  have : Mono i := by
    have : Mono ((FieldSheaf.forget X).map (kernel.ι c)) := inferInstance
    infer_instance
  refine isZero_of_mono_openImmersionLowerShriek _ j i ?_
  refine IsZero.of_iso ?_ ((upperStarIsoOpenImmersionRestriction _ j).app _).symm
  change IsZero ((FieldSheaf.forget U).obj ((j)^*ᶠ[Λ].obj (kernel c)))
  exact (FieldSheaf.forget U).map_isZero
    ((isZero_kernel_of_mono ((j)^*ᶠ[Λ].map c)).of_iso (PreservesKernel.iso (j)^*ᶠ[Λ] c))

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

variable (Λ : Type) [NormedCommRing Λ] [IsUltrametricDist Λ]

variable {k : Type u} [Field k] [Finite k] {X₀ Y₀ : Scheme.{u}} {f : X₀ ⟶ Spec (.of k)}
  {g : Y₀ ⟶ Spec (.of k)} (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f) [IsOpenImmersion φ]

/-- The pullback along the base change `φ̄` of an open immersion commutes with the pushforwards
along the Frobenii: `(Fr_Y)_* ⋙ φ̄^* ≅ φ̄^* ⋙ (Fr_X)_*`. -/
noncomputable def fieldOpenImmersionUpperStarGeometricFiberMapCompFrobeniusIso :
    (g.geometricGaloisFrobenius.asIso.hom)_*ᶠ[Λ] ⋙ (Scheme.Hom.geometricFiberMap φ h)^*ᶠ[Λ] ≅
      (Scheme.Hom.geometricFiberMap φ h)^*ᶠ[Λ] ⋙ (f.geometricGaloisFrobenius.asIso.hom)_*ᶠ[Λ] :=
  Functor.isoWhiskerRight
    (fieldUpperStarIsoLowerStarInv Λ g.geometricGaloisFrobenius.asIso.symm).symm _ ≪≫
    (fieldUpperStarComp Λ _ _).symm ≪≫
    fieldUpperStarCongr Λ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv φ h) ≪≫
    fieldUpperStarComp Λ _ _ ≪≫
    Functor.isoWhiskerLeft _ (fieldUpperStarIsoLowerStarInv Λ f.geometricGaloisFrobenius.asIso.symm)

/-- The extension by zero along the base change `φ̄` of an open immersion commutes with the
Frobenius pullbacks `Fr^* = (Fr⁻¹)_*`: the two sides are left adjoint to the two sides of
`AlgebraicGeometry.ProEtale.fieldOpenImmersionUpperStarGeometricFiberMapCompFrobeniusIso`. -/
noncomputable def fieldOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso :
    (Scheme.Hom.geometricFiberMap φ h)_!ᶠ[Λ] ⋙ (g.geometricGaloisFrobenius.asIso.inv)_*ᶠ[Λ] ≅
      (f.geometricGaloisFrobenius.asIso.inv)_*ᶠ[Λ] ⋙ (Scheme.Hom.geometricFiberMap φ h)_!ᶠ[Λ] :=
  (conjugateIsoEquiv
      ((fieldLowerStarEquivalence Λ f.geometricGaloisFrobenius.asIso.symm).toAdjunction.comp
        (fieldOpenImmersionLowerShriekAdjunction Λ _))
      ((fieldOpenImmersionLowerShriekAdjunction Λ _).comp
        (fieldLowerStarEquivalence Λ g.geometricGaloisFrobenius.asIso.symm).toAdjunction)).symm
    (fieldOpenImmersionUpperStarGeometricFiberMapCompFrobeniusIso Λ φ h).symm

omit [IsOpenImmersion φ] in
/-- The exchange isomorphism
`AlgebraicGeometry.ProEtale.fieldLowerStarGeometricFiberMapCompFrobeniusIso` for the pushforwards
is conjugate, under the adjunctions `φ̄^* ⊣ φ̄_*` composed with the Frobenius equivalences, to
`AlgebraicGeometry.ProEtale.fieldOpenImmersionUpperStarGeometricFiberMapCompFrobeniusIso` for the
pullbacks. Each of its five constituents is conjugate to the identity, to a composition
isomorphism or to a congruence isomorphism of pushforwards. -/
lemma conjugateEquiv_fieldOpenImmersionUpperStarGeometricFiberMapCompFrobeniusIso_inv :
    conjugateEquiv
        ((fieldLowerStarEquivalence Λ g.geometricGaloisFrobenius.asIso.symm).symm.toAdjunction.comp
          (fieldUpperStarLowerStarAdjunction Λ (Scheme.Hom.geometricFiberMap φ h)))
      ((fieldUpperStarLowerStarAdjunction Λ (Scheme.Hom.geometricFiberMap φ h)).comp
        (fieldLowerStarEquivalence Λ f.geometricGaloisFrobenius.asIso.symm).symm.toAdjunction)
      (fieldOpenImmersionUpperStarGeometricFiberMapCompFrobeniusIso Λ φ h).inv =
    (fieldLowerStarGeometricFiberMapCompFrobeniusIso Λ φ h).hom := by
  set j := Scheme.Hom.geometricFiberMap φ h
  set a := f.geometricGaloisFrobenius.asIso
  set b := g.geometricGaloisFrobenius.asIso
  set adj := fieldUpperStarLowerStarAdjunction Λ j
  have h₁ := conjugateEquiv_whiskerRight
    (fieldLowerStarEquivalence Λ b.symm).symm.toAdjunction
    (fieldUpperStarLowerStarAdjunction Λ (Iso.symm b).hom) adj
    (fieldUpperStarIsoLowerStarInv Λ b.symm).hom
  have h₂ : conjugateEquiv ((fieldUpperStarLowerStarAdjunction Λ (Iso.symm b).hom).comp adj)
      (fieldUpperStarLowerStarAdjunction Λ (j ≫ b.inv))
      (fieldUpperStarComp Λ j (Iso.symm b).hom).hom =
        (fieldLowerStarComp Λ j (Iso.symm b).hom).hom :=
    conjugateEquiv_fieldUpperStarComp_hom Λ j _
  have h₃ := conjugateEquiv_fieldUpperStarCongr_inv Λ
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv φ h)
  have h₄ : conjugateEquiv (fieldUpperStarLowerStarAdjunction Λ (a.inv ≫ j))
      (adj.comp (fieldUpperStarLowerStarAdjunction Λ (Iso.symm a).hom))
      (fieldUpperStarComp Λ a.inv j).inv = (fieldLowerStarComp Λ a.inv j).inv :=
    conjugateEquiv_fieldUpperStarComp_inv Λ a.inv j
  have h₅ := conjugateEquiv_whiskerLeft (fieldUpperStarLowerStarAdjunction Λ (Iso.symm a).hom)
    (fieldLowerStarEquivalence Λ a.symm).symm.toAdjunction adj
    (fieldUpperStarIsoLowerStarInv Λ a.symm).inv
  have hb : conjugateEquiv (fieldLowerStarEquivalence Λ b.symm).symm.toAdjunction
      (fieldUpperStarLowerStarAdjunction Λ (Iso.symm b).hom)
      (fieldUpperStarIsoLowerStarInv Λ b.symm).hom = 𝟙 ((Iso.symm b).hom)_*ᶠ[Λ] :=
    conjugateEquiv_leftAdjointUniq_hom _ _
  have ha : conjugateEquiv (fieldUpperStarLowerStarAdjunction Λ (Iso.symm a).hom)
      (fieldLowerStarEquivalence Λ a.symm).symm.toAdjunction
      (fieldUpperStarIsoLowerStarInv Λ a.symm).inv = 𝟙 _ :=
    conjugateEquiv_leftAdjointUniq_inv _ _
  rw [hb] at h₁
  rw [ha] at h₅
  simp only [fieldOpenImmersionUpperStarGeometricFiberMapCompFrobeniusIso, Iso.trans_inv,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv, Iso.symm_inv, Category.assoc]
  rw [← conjugateEquiv_comp _ (adj.comp (fieldUpperStarLowerStarAdjunction Λ (Iso.symm a).hom)) _,
    ← conjugateEquiv_comp _ (fieldUpperStarLowerStarAdjunction Λ (a.inv ≫ j)) _,
    ← conjugateEquiv_comp _ (fieldUpperStarLowerStarAdjunction Λ (j ≫ b.inv)) _,
    ← conjugateEquiv_comp _ ((fieldUpperStarLowerStarAdjunction Λ (Iso.symm b).hom).comp adj) _]
  rw [h₁, h₂, h₃, h₄, h₅]
  simp only [Functor.whiskerRight_id', Category.comp_id,
    fieldLowerStarGeometricFiberMapCompFrobeniusIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  -- `simp` does not see through the instance arguments here, and a plain `rfl` times out in the
  -- kernel.
  rw [show (j)_*ᶠ[Λ].whiskerLeft (𝟙 (b.inv)_*ᶠ[Λ]) = 𝟙 _ from Functor.whiskerLeft_id' _]
  exact Category.id_comp _

/-- The comparison `φ̄_! ⟶ φ̄_*` commutes with the Frobenius exchange isomorphisms. -/
lemma fieldOpenImmersionLowerShriekToLowerStar_geometricFiberMapCompFrobeniusIso :
    Functor.whiskerRight
        (fieldOpenImmersionLowerShriekToLowerStar Λ (Scheme.Hom.geometricFiberMap φ h))
        (g.geometricGaloisFrobenius.asIso.inv)_*ᶠ[Λ] ≫
      (fieldLowerStarGeometricFiberMapCompFrobeniusIso Λ φ h).hom =
    (fieldOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso Λ φ h).hom ≫
      Functor.whiskerLeft (f.geometricGaloisFrobenius.asIso.inv)_*ᶠ[Λ]
        (fieldOpenImmersionLowerShriekToLowerStar Λ (Scheme.Hom.geometricFiberMap φ h)) := by
  have := Adjunction.whiskerRight_comp_conjugateIsoEquiv_hom
    (fieldOpenImmersionLowerShriekAdjunction Λ (Scheme.Hom.geometricFiberMap φ h))
    (fieldUpperStarLowerStarAdjunction Λ (Scheme.Hom.geometricFiberMap φ h))
    (fieldLowerStarEquivalence Λ f.geometricGaloisFrobenius.asIso.symm).symm
    (fieldLowerStarEquivalence Λ g.geometricGaloisFrobenius.asIso.symm).symm
    (fieldOpenImmersionUpperStarGeometricFiberMapCompFrobeniusIso Λ φ h) _
    (fieldOpenImmersionLowerShriekAdjunction_unit_app_comp_map_lowerShriekToLowerStar _)
  rw [conjugateIsoEquiv_apply_hom, Iso.symm_hom,
    conjugateEquiv_fieldOpenImmersionUpperStarGeometricFiberMapCompFrobeniusIso_inv] at this
  exact this

end AlgebraicGeometry.ProEtale
