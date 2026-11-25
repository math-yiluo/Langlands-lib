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
public import WeilConjectures.SixFunctors.ProEtale.Adic.GeometricFrobenius
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Complement
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Mono

/-!
# Extension by zero of sheaves of modules over the constant `ℓ`-adic sheaf

For an open immersion `j : U ⟶ X`, the pullback `j^*` of sheaves of `ℚ̄_ℓ,X`-modules
(`AlgebraicGeometry.ProEtale.adicUpperStar`) preserves limits, its underlying functor being the
restriction along the localization functor. Hence it has a left adjoint, the extension by zero
`j_!` (`AlgebraicGeometry.ProEtale.adicOpenImmersionLowerShriek`), by the special adjoint functor
theorem in the Grothendieck abelian category of sheaves of `ℚ̄_ℓ,X`-modules. The pushforward `j_*`
is fully faithful (the counit of `j^* ⊣ j_*` is invertible), hence so is `j_!`, and `j_! F`
vanishes along every morphism missing the range of `j`.

On underlying sheaves, `j_!` is the extension by zero of sheaves
(`AlgebraicGeometry.ProEtale.adicOpenImmersionLowerShriekComparison`), hence exact. The point is
that the underlying sheaf of `j_! M` is an extension by zero, i.e. the counit of `j_! ⊣ j^*` on
sheaves is invertible there. For a free module `ℚ̄_ℓ,U ⊗ P` the underlying sheaf of `j_!` is
`ℚ̄_ℓ,X ⊗ j_! P`, the tensor product of a sheaf with a presheaf vanishing away from `U`,
sheafified; and every module is a cokernel of a morphism of free modules.

## Main definitions

- `AlgebraicGeometry.ProEtale.adicOpenImmersionLowerShriek`: `j_!`, with notation `(j)_!ᵃ[l]`.
- `AlgebraicGeometry.ProEtale.adicOpenImmersionLowerShriekComparison`: the comparison
  `j_! M.X ⟶ (j_! M).X`, an isomorphism, giving the exactness of `j_!`.
- `AlgebraicGeometry.ProEtale.adicOpenImmersionLowerShriekToLowerStar`: the comparison
  `j_! ⟶ j_*`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- A sheaf of `ℚ̄_ℓ,X`-modules whose underlying sheaf vanishes is zero. -/
lemma AdicSheaf.isZero_of_isZero_X {X : Scheme.{u}} {M : AdicSheaf l X} (h : IsZero M.X) :
    IsZero M :=
  ⟨fun _ ↦ ⟨⟨0⟩, fun _ ↦ Mod.hom_ext _ _ (h.eq_of_src _ _)⟩,
    fun _ ↦ ⟨⟨0⟩, fun _ ↦ Mod.hom_ext _ _ (h.eq_of_tgt _ _)⟩⟩

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

instance : PreservesLimits ((j)^*[WeilCoefficients.{u} l]) :=
  preservesLimits_of_natIso (upperStarIsoOpenImmersionRestriction _ j).symm

instance (X : Scheme.{u}) : PreservesLimits (AdicSheaf.forget (l := l) X) where
  preservesLimitsOfShape := inferInstance

instance : PreservesLimits ((j)^*ᵃ[l]) := by
  have : PreservesLimits ((j)^*ᵃ[l] ⋙ AdicSheaf.forget U) :=
    inferInstanceAs (PreservesLimits (AdicSheaf.forget X ⋙ (j)^*[WeilCoefficients.{u} l]))
  exact preservesLimits_of_reflects_of_preserves _ (AdicSheaf.forget U)

instance : (j)^*ᵃ[l].IsRightAdjoint :=
  isRightAdjoint_of_preservesLimits_of_isCoseparating (D := AdicSheaf l X)
    (isCoseparator_coseparator (AdicSheaf l X)) (j)^*ᵃ[l]

variable (l) in
/-- The extension by zero `j_!` of sheaves of modules over the constant `ℓ`-adic sheaves along an
open immersion `j`: the left adjoint of the pullback `j^*`. -/
noncomputable def adicOpenImmersionLowerShriek : AdicSheaf l U ⥤ AdicSheaf l X :=
  (j)^*ᵃ[l].leftAdjoint

@[inherit_doc adicOpenImmersionLowerShriek]
scoped notation "(" j ")_!ᵃ[" l "]" => adicOpenImmersionLowerShriek l j

variable (l) in
/-- The adjunction `j_! ⊣ j^*`. -/
noncomputable def adicOpenImmersionLowerShriekAdjunction : (j)_!ᵃ[l] ⊣ (j)^*ᵃ[l] :=
  Adjunction.ofIsRightAdjoint _

instance : (j)_!ᵃ[l].IsLeftAdjoint :=
  (adicOpenImmersionLowerShriekAdjunction l j).isLeftAdjoint

instance : (j)_!ᵃ[l].Additive :=
  (adicOpenImmersionLowerShriekAdjunction l j).left_adjoint_additive

instance : IsIso (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) j).counit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro N
  rw [← Adjunction.leftAdjointUniq_hom_app_counit (upperStarLowerStarAdjunction _ j)
    (openImmersionRestrictionLowerStarAdjunction _ j)]
  exact inferInstanceAs (IsIso ((upperStarIsoOpenImmersionRestriction _ j).hom.app _ ≫ _))

/-- The counit of `j^* ⊣ j_*` along an open immersion is invertible. -/
instance : IsIso (adicUpperStarLowerStarAdjunction l j).counit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro N
  have : IsIso ((adicUpperStarLowerStarAdjunction l j).counit.app N).hom := by
    rw [adicUpperStarLowerStarAdjunction, Adjunction.modAdjunction_counit_app_hom]
    infer_instance
  have : IsIso ((AdicSheaf.forget U).map ((adicUpperStarLowerStarAdjunction l j).counit.app N)) :=
    this
  exact isIso_of_reflects_iso _ (AdicSheaf.forget U)

/-- The unit of `j_! ⊣ j^*` along an open immersion is invertible: `j_!` is fully faithful, as
is `j_*`. -/
instance : IsIso (adicOpenImmersionLowerShriekAdjunction l j).unit :=
  (Adjunction.Triple.isIso_unit_iff_isIso_counit
    ⟨adicOpenImmersionLowerShriekAdjunction l j, adicUpperStarLowerStarAdjunction l j⟩).2
    inferInstance

/-- The tensor product of a sheaf with an extension by zero is again an extension by zero: the
counit of `j_! ⊣ j^*` is invertible at `B ⊗ j_! P`. Before sheafification, `B ⊗ j_! P` is the
tensor product of `B` with a presheaf vanishing away from `U`. -/
lemma isIso_openImmersionLowerShriek_counit_app_tensor
    {G : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l) ⥤
      Sheaf (Scheme.ProEt.topology U) (WeilCoefficients.{u} l)}
    (adj : (j)_!open[WeilCoefficients.{u} l] ⊣ G)
    (B : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l))
    (P : Sheaf (Scheme.ProEt.topology U) (WeilCoefficients.{u} l)) :
    IsIso (adj.counit.app (B ⊗ (j)_!open[WeilCoefficients.{u} l].obj P)) := by
  let L := (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).op
  let T := L.lan.obj P.obj
  have hR (W) (hW : IsEmpty (CostructuredArrow L W)) : IsZero ((B.obj ⊗ T).obj W) :=
    isZero_tensorObj_of_isZero_right _ (L.isInitialLanObjObj P.obj hW).isZero
  have e : B ⊗ (j)_!open[WeilCoefficients.{u} l].obj P ≅
      (presheafToSheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)).obj (B.obj ⊗ T) :=
    whiskerRightIso (asIso ((sheafificationAdjunction (Scheme.ProEt.topology X)
      (WeilCoefficients.{u} l)).counit.app B)).symm _ ≪≫
      Functor.Monoidal.μIso (presheafToSheaf (Scheme.ProEt.topology X)
        (WeilCoefficients.{u} l)) B.obj T
  exact adj.isIso_counit_app_of_iso
    (e ≪≫ presheafToSheafObjIsoOpenImmersionLowerShriek _ j _ hR)

/-- The counit of `j_! ⊣ j^*` on sheaves is invertible at the underlying sheaf of the extension by
zero `j_! M` of every sheaf of `ℚ̄_ℓ,U`-modules `M`. This holds for free modules, the extension by
zero of `ℚ̄_ℓ,U ⊗ P` being `ℚ̄_ℓ,X ⊗ j_! P`, and is inherited by cokernels, every module being a
cokernel of a morphism of free modules. -/
lemma isIso_openImmersionLowerShriekUpperStarAdjunction_counit_app_forget (M : AdicSheaf l U) :
    IsIso ((openImmersionLowerShriekUpperStarAdjunction (WeilCoefficients.{u} l) j).counit.app
      ((AdicSheaf.forget X).obj ((j)_!ᵃ[l].obj M))) := by
  let adj := openImmersionLowerShriekUpperStarAdjunction (WeilCoefficients.{u} l) j
  let S : ObjectProperty (AdicSheaf l U) := fun M ↦
    IsIso (adj.counit.app ((AdicSheaf.forget X).obj ((j)_!ᵃ[l].obj M)))
  have hiso {M N : AdicSheaf l U} (e : M ≅ N) (hM : S M) : S N := by
    have : IsIso (adj.counit.app ((AdicSheaf.forget X).obj ((j)_!ᵃ[l].obj M))) := hM
    exact NatTrans.isIso_app_of_iso adj.counit
      ((AdicSheaf.forget X).mapIso ((j)_!ᵃ[l].mapIso e)).symm
  have hfree (P : Sheaf (Scheme.ProEt.topology U) (WeilCoefficients.{u} l)) :
      S ((Mod.free _).obj P) := by
    let e := Adjunction.leftAdjointUniq
      ((Mod.freeForgetAdjunction (adicConstantSheaf l U)).comp
        (adicOpenImmersionLowerShriekAdjunction l j))
      (adj.comp (Mod.freeForgetAdjunction (adicConstantSheaf l X)))
    have : IsIso (adj.counit.app ((AdicSheaf.forget X).obj
        ((Mod.free (adicConstantSheaf l X)).obj ((j)_!open[WeilCoefficients.{u} l].obj P)))) :=
      isIso_openImmersionLowerShriek_counit_app_tensor j adj (adicConstantSheaf l X) P
    exact @NatTrans.isIso_app_of_iso _ _ _ _ _ _ adj.counit _ _
      ((AdicSheaf.forget X).mapIso (e.app P)) this
  have hcoker {M N : AdicSheaf l U} (f : M ⟶ N) (hM : S M) (hN : S N) : S (cokernel f) := by
    have : IsIso (adj.counit.app ((AdicSheaf.forget X).obj ((j)_!ᵃ[l].obj M))) := hM
    have : IsIso (adj.counit.app ((AdicSheaf.forget X).obj ((j)_!ᵃ[l].obj N))) := hN
    have : IsIso (adj.counit.app (cokernel (((j)_!ᵃ[l] ⋙ AdicSheaf.forget X).map f))) :=
      adj.isIso_counit_app_cokernel ((AdicSheaf.forget X).map ((j)_!ᵃ[l].map f))
    exact NatTrans.isIso_app_of_iso adj.counit
      (PreservesCokernel.iso ((j)_!ᵃ[l] ⋙ AdicSheaf.forget X) f)
  -- every module is a cokernel of a morphism of free modules
  let ε := (Mod.freeForgetAdjunction (adicConstantSheaf l U)).counit
  have hepi (N : AdicSheaf l U) : Epi (ε.app N) := by
    have : IsSplitEpi ((Mod.forget _).map (ε.app N)) :=
      ⟨⟨(λ_ N.X).inv ≫ MonObj.one ▷ N.X, Mod.unit_freeDesc _ (𝟙 N.X)⟩⟩
    exact (Mod.forget _).epi_of_epi_map inferInstance
  let p := ε.app M
  have e : M ≅ cokernel (ε.app (kernel p) ≫ kernel.ι p) :=
    (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel p)).coconePointUniqueUpToIso
      (colimit.isColimit _) ≪≫ (cokernelEpiComp _ _).symm
  exact hiso e.symm (hcoker _ (hfree _) (hfree _))

variable (l) in
/-- The comparison `j_! M.X ⟶ (j_! M).X` of the extension by zero of the underlying sheaf of a
sheaf of `ℚ̄_ℓ,U`-modules `M` with the underlying sheaf of its extension by zero. -/
noncomputable def adicOpenImmersionLowerShriekComparison :
    AdicSheaf.forget U ⋙ (j)_!open[WeilCoefficients.{u} l] ⟶ (j)_!ᵃ[l] ⋙ AdicSheaf.forget X :=
  Functor.whiskerRight (Functor.whiskerRight (adicOpenImmersionLowerShriekAdjunction l j).unit
      (AdicSheaf.forget U)) (j)_!open[WeilCoefficients.{u} l] ≫
    Functor.whiskerLeft ((j)_!ᵃ[l] ⋙ AdicSheaf.forget X)
      (openImmersionLowerShriekUpperStarAdjunction (WeilCoefficients.{u} l) j).counit

instance : IsIso (adicOpenImmersionLowerShriekComparison l j) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have := isIso_openImmersionLowerShriekUpperStarAdjunction_counit_app_forget j M
  dsimp [adicOpenImmersionLowerShriekComparison]
  infer_instance

/-- **Extension by zero is exact.** On underlying sheaves it is the extension by zero of
sheaves, which is exact. -/
instance : PreservesFiniteLimits (j)_!ᵃ[l] := by
  have : PreservesFiniteLimits ((j)_!ᵃ[l] ⋙ AdicSheaf.forget X) :=
    preservesFiniteLimits_of_natIso (asIso (adicOpenImmersionLowerShriekComparison l j))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (AdicSheaf.forget X)

/-- The pullback of `j_! F` along a morphism `g` missing the range of `j` vanishes: the
adjunctions turn `Hom(g^* j_! F, H)` into `Hom(F, j^* g_* H)`, and the underlying sheaf of
`j^* g_* H` vanishes. -/
lemma isZero_adicUpperStar_adicOpenImmersionLowerShriek {W : Scheme.{u}} (g : W ⟶ X)
    (hjg : Set.range j.base ∩ Set.range g.base = ∅) (F : AdicSheaf l U) :
    IsZero ((g)^*ᵃ[l].obj ((j)_!ᵃ[l].obj F)) := by
  have hz (H : AdicSheaf l W) : IsZero ((j)^*ᵃ[l].obj ((g)_*ᵃ[l].obj H)) :=
    AdicSheaf.isZero_of_isZero_X ((isZero_openImmersionRestriction_lowerStar _ g j
      (by rw [Set.inter_comm]; exact hjg) H.X).of_iso
        ((upperStarIsoOpenImmersionRestriction _ j).app _))
  refine (isZero_zero _).of_iso (IsInitial.uniqueUpToIso (IsInitial.ofUnique (h := fun H ↦ ?_))
    HasZeroObject.zeroIsInitial)
  haveI : Unique (F ⟶ (j)^*ᵃ[l].obj ((g)_*ᵃ[l].obj H)) :=
    ⟨⟨(hz H).isTerminal.from F⟩, fun _ ↦ (hz H).isTerminal.hom_ext _ _⟩
  exact Equiv.unique (((adicUpperStarLowerStarAdjunction l g).homEquiv _ H).trans
    ((adicOpenImmersionLowerShriekAdjunction l j).homEquiv F _))

variable (l) in
/-- The comparison `j_! ⟶ j_*` along an open immersion, from the adjoint triple
`j_! ⊣ j^* ⊣ j_*`: insert the inverse of the counit of `j^* ⊣ j_*` and contract with the counit
of `j_! ⊣ j^*`. -/
noncomputable def adicOpenImmersionLowerShriekToLowerStar : (j)_!ᵃ[l] ⟶ (j)_*ᵃ[l] :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (inv (adicUpperStarLowerStarAdjunction l j).counit) (j)_!ᵃ[l] ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (j)_*ᵃ[l] (adicOpenImmersionLowerShriekAdjunction l j).counit ≫
    (Functor.rightUnitor _).hom

/-- The comparison `j_! ⟶ j_*` is characterised by its transpose under `j_! ⊣ j^*`: the inverse
of the counit of `j^* ⊣ j_*`. -/
lemma adicOpenImmersionLowerShriekAdjunction_unit_app_comp_map_lowerShriekToLowerStar
    (F : AdicSheaf l U) :
    (adicOpenImmersionLowerShriekAdjunction l j).unit.app F ≫
        (j)^*ᵃ[l].map ((adicOpenImmersionLowerShriekToLowerStar l j).app F) =
      inv ((adicUpperStarLowerStarAdjunction l j).counit.app F) := by
  simp only [adicOpenImmersionLowerShriekToLowerStar, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.leftUnitor_inv_app,
    Functor.associator_hom_app, Functor.rightUnitor_hom_app, Category.id_comp, Functor.map_comp]
  erw [(adicOpenImmersionLowerShriekAdjunction l j).unit_naturality_assoc,
    (adicOpenImmersionLowerShriekAdjunction l j).right_triangle_components_assoc ((j)_*ᵃ[l].obj F),
    CategoryTheory.Functor.map_id, Category.comp_id]
  exact NatIso.isIso_inv_app _ _

/-- **The comparison `j_! M ⟶ j_* M` is a monomorphism.** Its kernel `K` restricts to zero on
`U`, `j^*` of the comparison being invertible, and its underlying sheaf is a subsheaf of the
extension by zero of the underlying sheaf of `M`; such a subsheaf vanishes
(`AlgebraicGeometry.ProEtale.isZero_of_mono_openImmersionLowerShriek`). -/
instance mono_adicOpenImmersionLowerShriekToLowerStar_app (M : AdicSheaf l U) :
    Mono ((adicOpenImmersionLowerShriekToLowerStar l j).app M) := by
  let c := (adicOpenImmersionLowerShriekToLowerStar l j).app M
  have : IsIso ((j)^*ᵃ[l].map c) := by
    have : IsIso ((adicOpenImmersionLowerShriekAdjunction l j).unit.app M ≫ (j)^*ᵃ[l].map c) := by
      rw [adicOpenImmersionLowerShriekAdjunction_unit_app_comp_map_lowerShriekToLowerStar]
      infer_instance
    exact IsIso.of_isIso_comp_left ((adicOpenImmersionLowerShriekAdjunction l j).unit.app M) _
  refine Preadditive.mono_of_isZero_kernel _ (AdicSheaf.isZero_of_isZero_X ?_)
  let i : (kernel c).X ⟶ (j)_!open[WeilCoefficients.{u} l].obj M.X :=
    (AdicSheaf.forget X).map (kernel.ι c) ≫ inv ((adicOpenImmersionLowerShriekComparison l j).app M)
  have : Mono i := by
    have : Mono ((AdicSheaf.forget X).map (kernel.ι c)) := inferInstance
    infer_instance
  refine isZero_of_mono_openImmersionLowerShriek _ j i ?_
  refine IsZero.of_iso ?_ ((upperStarIsoOpenImmersionRestriction _ j).app _).symm
  change IsZero ((AdicSheaf.forget U).obj ((j)^*ᵃ[l].obj (kernel c)))
  exact (AdicSheaf.forget U).map_isZero
    ((isZero_kernel_of_mono ((j)^*ᵃ[l].map c)).of_iso (PreservesKernel.iso (j)^*ᵃ[l] c))

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime]

variable {k : Type u} [Field k] [Finite k] {X₀ Y₀ : Scheme.{u}} {f : X₀ ⟶ Spec (.of k)}
  {g : Y₀ ⟶ Spec (.of k)} (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f) [IsOpenImmersion φ]

/-- The pullback along the base change `φ̄` of an open immersion commutes with the pushforwards
along the Frobenii: `(Fr_Y)_* ⋙ φ̄^* ≅ φ̄^* ⋙ (Fr_X)_*`. -/
noncomputable def adicOpenImmersionUpperStarGeometricFiberMapCompFrobeniusIso :
    (g.geometricGaloisFrobenius.asIso.hom)_*ᵃ[l] ⋙ (Scheme.Hom.geometricFiberMap φ h)^*ᵃ[l] ≅
      (Scheme.Hom.geometricFiberMap φ h)^*ᵃ[l] ⋙ (f.geometricGaloisFrobenius.asIso.hom)_*ᵃ[l] :=
  Functor.isoWhiskerRight
    (adicUpperStarIsoLowerStarInv l g.geometricGaloisFrobenius.asIso.symm).symm _ ≪≫
    (adicUpperStarComp l _ _).symm ≪≫
    adicUpperStarCongr l (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv φ h) ≪≫
    adicUpperStarComp l _ _ ≪≫
    Functor.isoWhiskerLeft _ (adicUpperStarIsoLowerStarInv l f.geometricGaloisFrobenius.asIso.symm)

/-- The extension by zero along the base change `φ̄` of an open immersion commutes with the
Frobenius pullbacks `Fr^* = (Fr⁻¹)_*`: the two sides are left adjoint to the two sides of
`AlgebraicGeometry.ProEtale.adicOpenImmersionUpperStarGeometricFiberMapCompFrobeniusIso`. -/
noncomputable def adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso :
    (Scheme.Hom.geometricFiberMap φ h)_!ᵃ[l] ⋙ (g.geometricGaloisFrobenius.asIso.inv)_*ᵃ[l] ≅
      (f.geometricGaloisFrobenius.asIso.inv)_*ᵃ[l] ⋙ (Scheme.Hom.geometricFiberMap φ h)_!ᵃ[l] :=
  (conjugateIsoEquiv
      ((adicLowerStarEquivalence l f.geometricGaloisFrobenius.asIso.symm).toAdjunction.comp
        (adicOpenImmersionLowerShriekAdjunction l _))
      ((adicOpenImmersionLowerShriekAdjunction l _).comp
        (adicLowerStarEquivalence l g.geometricGaloisFrobenius.asIso.symm).toAdjunction)).symm
    (adicOpenImmersionUpperStarGeometricFiberMapCompFrobeniusIso l φ h).symm

omit [IsOpenImmersion φ] in
/-- The exchange isomorphism
`AlgebraicGeometry.ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso` for the pushforwards
is conjugate, under the adjunctions `φ̄^* ⊣ φ̄_*` composed with the Frobenius equivalences, to
`AlgebraicGeometry.ProEtale.adicOpenImmersionUpperStarGeometricFiberMapCompFrobeniusIso` for the
pullbacks. Each of its five constituents is conjugate to the identity, to a composition
isomorphism or to a congruence isomorphism of pushforwards. -/
lemma conjugateEquiv_adicOpenImmersionUpperStarGeometricFiberMapCompFrobeniusIso_inv :
    conjugateEquiv
        ((adicLowerStarEquivalence l g.geometricGaloisFrobenius.asIso.symm).symm.toAdjunction.comp
          (adicUpperStarLowerStarAdjunction l (Scheme.Hom.geometricFiberMap φ h)))
      ((adicUpperStarLowerStarAdjunction l (Scheme.Hom.geometricFiberMap φ h)).comp
        (adicLowerStarEquivalence l f.geometricGaloisFrobenius.asIso.symm).symm.toAdjunction)
      (adicOpenImmersionUpperStarGeometricFiberMapCompFrobeniusIso l φ h).inv =
    (adicLowerStarGeometricFiberMapCompFrobeniusIso l φ h).hom := by
  set j := Scheme.Hom.geometricFiberMap φ h
  set a := f.geometricGaloisFrobenius.asIso
  set b := g.geometricGaloisFrobenius.asIso
  set adj := adicUpperStarLowerStarAdjunction l j
  have h₁ := conjugateEquiv_whiskerRight
    (adicLowerStarEquivalence l b.symm).symm.toAdjunction
    (adicUpperStarLowerStarAdjunction l (Iso.symm b).hom) adj
    (adicUpperStarIsoLowerStarInv l b.symm).hom
  have h₂ : conjugateEquiv ((adicUpperStarLowerStarAdjunction l (Iso.symm b).hom).comp adj)
      (adicUpperStarLowerStarAdjunction l (j ≫ b.inv))
      (adicUpperStarComp l j (Iso.symm b).hom).hom = (adicLowerStarComp l j (Iso.symm b).hom).hom :=
    conjugateEquiv_adicUpperStarComp_hom l j _
  have h₃ := conjugateEquiv_adicUpperStarCongr_inv l
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv φ h)
  have h₄ : conjugateEquiv (adicUpperStarLowerStarAdjunction l (a.inv ≫ j))
      (adj.comp (adicUpperStarLowerStarAdjunction l (Iso.symm a).hom))
      (adicUpperStarComp l a.inv j).inv = (adicLowerStarComp l a.inv j).inv :=
    conjugateEquiv_adicUpperStarComp_inv l a.inv j
  have h₅ := conjugateEquiv_whiskerLeft (adicUpperStarLowerStarAdjunction l (Iso.symm a).hom)
    (adicLowerStarEquivalence l a.symm).symm.toAdjunction adj
    (adicUpperStarIsoLowerStarInv l a.symm).inv
  have hb : conjugateEquiv (adicLowerStarEquivalence l b.symm).symm.toAdjunction
      (adicUpperStarLowerStarAdjunction l (Iso.symm b).hom)
      (adicUpperStarIsoLowerStarInv l b.symm).hom = 𝟙 ((Iso.symm b).hom)_*ᵃ[l] :=
    conjugateEquiv_leftAdjointUniq_hom _ _
  have ha : conjugateEquiv (adicUpperStarLowerStarAdjunction l (Iso.symm a).hom)
      (adicLowerStarEquivalence l a.symm).symm.toAdjunction
      (adicUpperStarIsoLowerStarInv l a.symm).inv = 𝟙 _ :=
    conjugateEquiv_leftAdjointUniq_inv _ _
  rw [hb] at h₁
  rw [ha] at h₅
  simp only [adicOpenImmersionUpperStarGeometricFiberMapCompFrobeniusIso, Iso.trans_inv,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv, Iso.symm_inv, Category.assoc]
  rw [← conjugateEquiv_comp _ (adj.comp (adicUpperStarLowerStarAdjunction l (Iso.symm a).hom)) _,
    ← conjugateEquiv_comp _ (adicUpperStarLowerStarAdjunction l (a.inv ≫ j)) _,
    ← conjugateEquiv_comp _ (adicUpperStarLowerStarAdjunction l (j ≫ b.inv)) _,
    ← conjugateEquiv_comp _ ((adicUpperStarLowerStarAdjunction l (Iso.symm b).hom).comp adj) _]
  rw [h₁, h₂, h₃, h₄, h₅]
  simp only [Functor.whiskerRight_id', Category.comp_id,
    adicLowerStarGeometricFiberMapCompFrobeniusIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  -- `simp` does not see through the instance arguments here, and a plain `rfl` times out in the
  -- kernel.
  rw [show (j)_*ᵃ[l].whiskerLeft (𝟙 (b.inv)_*ᵃ[l]) = 𝟙 _ from Functor.whiskerLeft_id' _]
  exact Category.id_comp _

/-- The comparison `φ̄_! ⟶ φ̄_*` commutes with the Frobenius exchange isomorphisms. -/
lemma adicOpenImmersionLowerShriekToLowerStar_geometricFiberMapCompFrobeniusIso :
    Functor.whiskerRight
        (adicOpenImmersionLowerShriekToLowerStar l (Scheme.Hom.geometricFiberMap φ h))
        (g.geometricGaloisFrobenius.asIso.inv)_*ᵃ[l] ≫
      (adicLowerStarGeometricFiberMapCompFrobeniusIso l φ h).hom =
    (adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso l φ h).hom ≫
      Functor.whiskerLeft (f.geometricGaloisFrobenius.asIso.inv)_*ᵃ[l]
        (adicOpenImmersionLowerShriekToLowerStar l (Scheme.Hom.geometricFiberMap φ h)) := by
  have := Adjunction.whiskerRight_comp_conjugateIsoEquiv_hom
    (adicOpenImmersionLowerShriekAdjunction l (Scheme.Hom.geometricFiberMap φ h))
    (adicUpperStarLowerStarAdjunction l (Scheme.Hom.geometricFiberMap φ h))
    (adicLowerStarEquivalence l f.geometricGaloisFrobenius.asIso.symm).symm
    (adicLowerStarEquivalence l g.geometricGaloisFrobenius.asIso.symm).symm
    (adicOpenImmersionUpperStarGeometricFiberMapCompFrobeniusIso l φ h) _
    (adicOpenImmersionLowerShriekAdjunction_unit_app_comp_map_lowerShriekToLowerStar _)
  rw [conjugateIsoEquiv_apply_hom, Iso.symm_hom,
    conjugateEquiv_adicOpenImmersionUpperStarGeometricFiberMapCompFrobeniusIso_inv] at this
  exact this

end AlgebraicGeometry.ProEtale
