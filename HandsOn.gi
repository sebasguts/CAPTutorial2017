#! @Title CAP Hands-on $\Q$-vector spaces
#! @Author Sebastian Gutsche, Sebastian Posur

#! @Chapter HandsOn

#! @Section Objects and morphisms

LoadPackage( "CAP" );

LoadPackage( "MatricesForHomalg" );

#################################
##
## Technical declarations
##
#################################

## Objects
DeclareCategory( "IsQVectorSpace",
                 IsCapCategoryObject );

DeclareRepresentation( "IsQVectorSpaceRep",
                       IsQVectorSpace and IsAttributeStoringRep,
                       [ ] );

BindGlobal( "TheFamilyOfQVectorSpaces",
            NewFamily( "TheFamilyOfQVectorSpaces" ) );

BindGlobal( "TheTypeOfQVectorSpaces",
        NewType( TheFamilyOfQVectorSpaces,
                IsQVectorSpaceRep ) );

## Morphisms
DeclareCategory( "IsQVectorSpaceMorphism",
                 IsCapCategoryMorphism );

DeclareRepresentation( "IsQVectorSpaceMorphismRep",
                       IsQVectorSpaceMorphism and IsAttributeStoringRep,
                       [ ] );

BindGlobal( "TheFamilyOfQVectorSpaceMorphisms",
            NewFamily( "TheFamilyOfQVectorSpaceMorphisms" ) );

BindGlobal( "TheTypeOfQVectorSpaceMorphisms",
        NewType( TheFamilyOfQVectorSpaceMorphisms,
                  IsQVectorSpaceMorphismRep ) );

#################################
##
## Attributes
##
#################################

#! @Description
#! The argument is an object $V$ in the category of rational vector spaces.
#! The output is its dimension.
#! @Returns a non-negative integer
#! @Arguments V
DeclareAttribute( "Dimension",
                  IsQVectorSpace );

#! @Description
#! The argument is a morphism $\alpha$ in the category of rational vector spaces.
#! The output is its underlying matrix.
#! @Returns a homalg matrix
#! @Arguments alpha
DeclareAttribute( "UnderlyingMatrix",
                  IsQVectorSpaceMorphism );

#################################
##
## Operations
##
#################################

#! @Description
#! The argument is a non-negative integer $d$.
#! The output is a rational vector space of dimension $d$.
#! @Returns an object
#! @Arguments d
DeclareOperation( "QVectorSpace",
                  [ IsInt ] );

#! @Description
#! The first argument is a rational vector space $V$.
#! The second argument $A$ is either a homalg matrix defined over the rationals
#! or an input that can be used as the first argument in the HomalgMatrix constructor.
#! The third argument is a rational vector space $W$.
#! The output is vector space morphism from $V$ to $W$ defined by $A$.
#! @Returns an morphism in $\mathrm{Hom}(V,W)$
#! @Arguments V,A,W
DeclareOperation( "QVectorSpaceMorphism",
                  [ IsQVectorSpace, IsObject, IsQVectorSpace ] );

#################################
##
## Creation of category
##
#################################

BindGlobal( "vecspaces", CreateCapCategory( "QVectorSpaces" ) );

SetIsAbelianCategory( vecspaces, true );

#################################
##
## Creation of Q
##
#################################

BindGlobal( "VECTORSPACES_FIELD", HomalgFieldOfRationals( ) );

#################################
##
## Constructors for objects and morphisms
##
#################################

##
InstallMethod( QVectorSpace,
               [ IsInt ],
               
  function( dim )
    local space;
    
    if dim < 0 then
        
        Error( "the argument has to be a non-negative integer" );
        
    fi;
    
    space := rec( );
    
    ObjectifyWithAttributes( space, TheTypeOfQVectorSpaces,
                             Dimension, dim 
    );
    
    Add( vecspaces, space );
    
    return space;
    
end );

##
InstallMethod( QVectorSpaceMorphism,
                  [ IsQVectorSpaceRep, IsObject, IsQVectorSpaceRep ],
                  
  function( source, matrix, range )
    local morphism;
    
    if not IsHomalgMatrix( matrix ) then
      
      matrix := HomalgMatrix( matrix, Dimension( source ), Dimension( range ), VECTORSPACES_FIELD );
      
    fi;
    
    morphism := rec( );
    
    ObjectifyWithAttributes( morphism, TheTypeOfQVectorSpaceMorphisms,
                             Source, source,
                             Range, range,
                             UnderlyingMatrix, matrix
    );
    
    Add( vecspaces, morphism );
    
    return morphism;
    
end );

#################################
##
## View
##
#################################

##
InstallMethod( ViewObj,
               [ IsQVectorSpaceRep ],
               
  function( obj )
    
    Print( "<A rational vector space of dimension ", String( Dimension( obj ) ), ">" );
    
end );

##
InstallMethod( ViewObj,
               [ IsQVectorSpaceMorphismRep ],
               
  function( mor )
    
    Print( "A rational vector space homomorphism with matrix: \n" );
    
    Display( UnderlyingMatrix( mor ) );
    
end );

#################################
##
## Functions to be added to category
##
#################################

##
identity_morphism := function( obj )
    
    return QVectorSpaceMorphism( obj, HomalgIdentityMatrix( Dimension( obj ), VECTORSPACES_FIELD ), obj );
    
end;

AddIdentityMorphism( vecspaces, identity_morphism );

##
pre_compose := function( mor_left, mor_right )
    local composition;
    
    composition := UnderlyingMatrix( mor_left ) * UnderlyingMatrix( mor_right );
    
    return QVectorSpaceMorphism( Source( mor_left ), composition, Range( mor_right ) );
    
end;

AddPreCompose( vecspaces, pre_compose );

##
is_equal_for_objects := function( vecspace_1, vecspace_2 )
    
    return Dimension( vecspace_1 ) = Dimension( vecspace_2 );
    
end;

AddIsEqualForObjects( vecspaces, is_equal_for_objects );

##
is_equal_for_morphisms := function( a, b )
    
    return UnderlyingMatrix( a ) = UnderlyingMatrix( b );
    
end;

AddIsEqualForMorphisms( vecspaces, is_equal_for_morphisms );

##
kernel_emb := function( morphism )
    local syzygies, kernel_obj;
    
    syzygies := SyzygiesOfRows( UnderlyingMatrix( morphism ) );
    
    kernel_obj := QVectorSpace( NrRows( syzygies ) );
    
    return QVectorSpaceMorphism( kernel_obj, syzygies, Source( morphism ) );
    
end;

AddKernelEmbedding( vecspaces, kernel_emb );

##
lift := function( alpha, beta )
    local solution;
    
    solution := RightDivide( UnderlyingMatrix( alpha ), UnderlyingMatrix( beta ) );
    
    if solution = fail then
        
        return fail;
        
    fi;
    
    return QVectorSpaceMorphism( Source( alpha ),
           solution,
           Source( beta ) );
    
end;

AddLift( vecspaces, lift );

##
cokernel_proj := function( morphism )
    local syzygies, cokernel_obj;
    
    syzygies := SyzygiesOfColumns( UnderlyingMatrix( morphism ) );
    
    cokernel_obj := QVectorSpace( NrColumns( syzygies ) );
    
    return QVectorSpaceMorphism( Range( morphism ), 
              syzygies, cokernel_obj );
    
end;

AddCokernelProjection( vecspaces, cokernel_proj );

##
colift := function( alpha, beta )
    local solution;
    
    solution := LeftDivide( UnderlyingMatrix( alpha ), UnderlyingMatrix( beta ) );
    
    if solution = fail then
        
        return fail;
        
    fi;
    
    return QVectorSpaceMorphism( Range( alpha ),
              solution,
              Range( beta ) );
    
end;

AddColift( vecspaces, colift );

##
zero_object := function( )
    
    return QVectorSpace( 0 );
    
end;

AddZeroObject( vecspaces, zero_object );

##
universal_morphism_into_zero_object := function( source )
    
    return QVectorSpaceMorphism( source,
              HomalgZeroMatrix( Dimension( source ), 0, VECTORSPACES_FIELD ),
              QVectorSpace( 0 ) );
    
end;

AddUniversalMorphismIntoZeroObject( vecspaces, universal_morphism_into_zero_object );

##
universal_morphism_into_zero_object_with_given_zero_object := function( source, terminal_object )
    
    return QVectorSpaceMorphism( source,
              HomalgZeroMatrix( Dimension( source ), 0, VECTORSPACES_FIELD ),
              terminal_object );
    
end;

AddUniversalMorphismIntoZeroObjectWithGivenZeroObject( vecspaces, universal_morphism_into_zero_object_with_given_zero_object );

##
universal_morphism_from_zero_object := function( sink )
    
    return QVectorSpaceMorphism( QVectorSpace( 0 ),
              HomalgZeroMatrix( 0, Dimension( sink ), VECTORSPACES_FIELD ),
              sink );
    
end;

AddUniversalMorphismFromZeroObject( vecspaces, universal_morphism_from_zero_object );

##
universal_morphism_from_zero_object_with_given_zero_object := function( sink, initial_object )
    
    return QVectorSpaceMorphism( initial_object,
                   HomalgZeroMatrix( 0, Dimension( sink ), VECTORSPACES_FIELD ),
                   sink );
    
end;

AddUniversalMorphismFromZeroObjectWithGivenZeroObject( vecspaces, universal_morphism_from_zero_object_with_given_zero_object );

##
addition_for_morphisms := function( a, b )
    
    return QVectorSpaceMorphism( Source( a ),
              UnderlyingMatrix( a ) + UnderlyingMatrix( b ),
              Range( a ) );
    
end;

AddAdditionForMorphisms( vecspaces, addition_for_morphisms );

##
additive_inverse_for_morphisms := function( a )
    
    return QVectorSpaceMorphism( Source( a ),
              - UnderlyingMatrix( a ),
              Range( a ) );
    
end;

AddAdditiveInverseForMorphisms( vecspaces, additive_inverse_for_morphisms );

##
direct_sum := function( object_product_list )
    local dim;
    
    dim := Sum( List( object_product_list, c -> Dimension( c ) ) );
    
    return QVectorSpace( dim );
  
end;

AddDirectSum( vecspaces, direct_sum );

##
injection_of_cofactor_of_direct_sum := function( object_product_list, injection_number )
    local components, dim, dim_pre, dim_post, dim_cofactor, coproduct, number_of_objects, injection_of_cofactor;
    
    components := object_product_list;
    
    number_of_objects := Length( components );
    
    dim := Sum( components, c -> Dimension( c ) );
    
    dim_pre := Sum( components{ [ 1 .. injection_number - 1 ] }, c -> Dimension( c ) );
    
    dim_post := Sum( components{ [ injection_number + 1 .. number_of_objects ] }, c -> Dimension( c ) );
    
    dim_cofactor := Dimension( object_product_list[ injection_number ] );
    
    coproduct := QVectorSpace( dim );
    
    injection_of_cofactor := HomalgZeroMatrix( dim_cofactor, dim_pre ,VECTORSPACES_FIELD );
    
    injection_of_cofactor := UnionOfColumns( injection_of_cofactor, 
                                         HomalgIdentityMatrix( dim_cofactor, VECTORSPACES_FIELD ) );
    
    injection_of_cofactor := UnionOfColumns( injection_of_cofactor, 
                                         HomalgZeroMatrix( dim_cofactor, dim_post, VECTORSPACES_FIELD ) );
    
    return QVectorSpaceMorphism( object_product_list[ injection_number ], injection_of_cofactor, coproduct );
    
end;

AddInjectionOfCofactorOfDirectSum( vecspaces, injection_of_cofactor_of_direct_sum );

##
universal_morphism_from_direct_sum := function( diagram, sink )
    local dim, coproduct, components, universal_morphism, morphism;
    
    components := sink;
    
    dim := Sum( components, c -> Dimension( Source( c ) ) );
    
    coproduct := QVectorSpace( dim );
    
    universal_morphism := UnderlyingMatrix( sink[1] );
    
    for morphism in components{ [ 2 .. Length( components ) ] } do
    
      universal_morphism := UnionOfRows( universal_morphism, UnderlyingMatrix( morphism ) );
    
    od;
    
    return QVectorSpaceMorphism( coproduct, universal_morphism, Range( sink[1] ) );
    
end;

AddUniversalMorphismFromDirectSum( vecspaces, universal_morphism_from_direct_sum );

##
projection_in_factor_of_direct_sum := function( object_product_list, projection_number )
    local components, dim, dim_pre, dim_post, dim_factor, direct_product, number_of_objects, projection_in_factor;
    
    components := object_product_list;
    
    number_of_objects := Length( components );
    
    dim := Sum( components, c -> Dimension( c ) );
    
    dim_pre := Sum( components{ [ 1 .. projection_number - 1 ] }, c -> Dimension( c ) );
    
    dim_post := Sum( components{ [ projection_number + 1 .. number_of_objects ] }, c -> Dimension( c ) );
    
    dim_factor := Dimension( object_product_list[ projection_number ] );
    
    direct_product := QVectorSpace( dim );
    
    projection_in_factor := HomalgZeroMatrix( dim_pre, dim_factor, VECTORSPACES_FIELD );
    
    projection_in_factor := UnionOfRows( projection_in_factor, 
                                         HomalgIdentityMatrix( dim_factor, VECTORSPACES_FIELD ) );
    
    projection_in_factor := UnionOfRows( projection_in_factor, 
                                         HomalgZeroMatrix( dim_post, dim_factor, VECTORSPACES_FIELD ) );
    
    return QVectorSpaceMorphism( direct_product, projection_in_factor, object_product_list[ projection_number ] );
    
end;

AddProjectionInFactorOfDirectSum( vecspaces, projection_in_factor_of_direct_sum );

##
universal_morphism_into_direct_sum := function( diagram, sink )
    local dim, direct_product, components, universal_morphism, morphism;
    
    components := sink;
    
    dim := Sum( components, c -> Dimension( Range( c ) ) );
    
    direct_product := QVectorSpace( dim );
    
    universal_morphism := UnderlyingMatrix( sink[1] );
    
    for morphism in components{ [ 2 .. Length( components ) ] } do
    
      universal_morphism := UnionOfColumns( universal_morphism, UnderlyingMatrix( morphism ) );
    
    od;
    
    return QVectorSpaceMorphism( Source( sink[1] ), universal_morphism, direct_product );
    
end;

AddUniversalMorphismIntoDirectSum( vecspaces, universal_morphism_into_direct_sum );

#################################
##
## Finalize category
##
#################################

Finalize( vecspaces );

#################################
##
## Test the basic operations
##
#################################

# Creating objects and morphisms

V := QVectorSpace( 2 );

CapCategory( V );

Dimension( V );

W := QVectorSpace( 3 );

alpha := QVectorSpaceMorphism( V, [ [ 1, 1, 1 ], [ -1, -1, -1 ] ], W );

CapCategory( alpha );

UnderlyingMatrix( alpha );

# Testing the KernelEmbedding

KernelEmbedding( alpha );

KernelObject( alpha );

# Computing an intersection

M1 := QVectorSpace( 2 );

M2 := QVectorSpace( 2 );

N := QVectorSpace( 3 );

iota1 := QVectorSpaceMorphism( M1, [ [ 1, 0, 0 ], [ 0, 1, 1 ] ], N );

IsMonomorphism( iota1 );

iota2 := QVectorSpaceMorphism( M2, [ [ 1, 1, 0 ], [ 0, 0, 1 ] ], N );

IsMonomorphism( iota2 );

pi1 := ProjectionInFactorOfDirectSum( [ M1, M2 ], 1 );

pi2 := ProjectionInFactorOfDirectSum( [ M1, M2 ], 2 );

lambda := PostCompose( iota1, pi1 );

phi := lambda - PostCompose( iota2, pi2 );

kappa := KernelEmbedding( phi );

PostCompose( lambda, kappa );

PreCompose( ProjectionInFactorOfFiberProduct( [ iota1, iota2 ], 1 ), iota1 );

#################################
##
## A function for computing homology
##
#################################

HomologyObject := function( alpha, beta )
  local iota, lambda;
  
  if not IsZero( PreCompose( alpha, beta ) ) then
      
      Error( "the composition of the given morphisms has to be zero" );
      
  fi;
  
  iota := ImageEmbedding( alpha );
  
  lambda := KernelLift( beta, iota );
  
  return CokernelObject( lambda );
  
end;

HomologyObject( alpha, CokernelProjection( alpha ) );

HomologyObject( KernelEmbedding( alpha ), alpha );

pi1 := ProjectionInFactorOfDirectSum( [ V, V, V ], 1 );

iota1 := InjectionOfCofactorOfDirectSum( [ V, V, V ], 1 );

pi2 := ProjectionInFactorOfDirectSum( [ V, V, V ], 2 );

iota2 := InjectionOfCofactorOfDirectSum( [ V, V, V ], 2 );

HomologyObject( PreCompose( pi1, iota1 ), PreCompose( pi2, iota2 ) );
