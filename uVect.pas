unit uVect;
{$MODE objfpc}{$H+}
{$INLINE ON}
{$modeswitch advancedrecords}
{$codepage utf8} // ← これを追加！

interface

uses
   {$ifdef unix}
   cthreads,cmem,
   cwstring, // ← Linux/Unix環境でUTF-8(System/WideString)を正しく扱うために必須
   {$endif}
   sysutils,uBMP,fpImage,math;

const
   MAX_WORD = High(WORD);//FPColor.redと書きたいが難しい？
   rev_max_word= 1/MAX_WORD;
   eps=1e-4;
   INF=1e20;

type
   RandomRecord = record
   private
      const
         N = 624;
         MATRIX_A = $9908B0DF;
         UPPER_MASK = $80000000;
         LOWER_MASK = $7FFFFFFF;
      var
         FState: array[0..N - 1] of Cardinal;
         FIndex: Integer;
         procedure Twist;inline;
   public
      constructor Create(seed_: Cardinal);
      function Random: real;inline;
   end;

   Vec3=record
      x,y,z:real;
      class function new(x_,y_,z_:real):Vec3;static;inline;
      function Norm:Vec3;inline;
      function len:real;inline;
      function Dot(const V2 :Vec3):real;inline;//内積
      function Cross(const V2 :Vec3):Vec3;inline;//外積
      function Mult(const V2:Vec3):Vec3;inline;
      function Neg:Vec3;
      class operator * (const v1: Vec3; const r: real): Vec3; inline;
      class operator / (const v1: Vec3; const r: real): Vec3; inline;
      class operator * (const v1, v2: Vec3): real; inline; // 内積
      class operator / (const v1, v2: Vec3): Vec3; inline; // 外積
      class operator + (const v1, v2: Vec3): Vec3; inline;
      class operator - (const v1, v2: Vec3): Vec3; inline;
      class operator + (const v1: Vec3; const r: real): Vec3; inline;
      class operator - (const v1: Vec3; const r: real): Vec3; inline;
      property r: Real read x write x;
      property g: Real read y write y;
      property b: Real read z write z;
   end;
   
   RayRecord=record
      o, d:Vec3;
      class function new(o_,d_:Vec3):RayRecord;static;
   end;
    
   CamRecord=record
      o,d:Vec3;
      PlaneDist:real;
      w,h,samps:integer;
      cx,cy:Vec3;
      class function new(o_,d_:Vec3;w_,h_,samps_:integer):CamRecord;static;
      function GetRay(x,y,sx,sy:integer):RayRecord;
      procedure CamWrite;
   end;

   Vec2=record
      u,v:real;
      function DirToUV(d:Vec3):Vec2;
   end;
      
   function ClampVector(v:Vec3):Vec3;
   function ColToRGB(v:Vec3):TFPColor;
   function RGBtoColor(c:TFPColor):Vec3;inline;
const
   BackGroundColor:Vec3 = (x:0;y:0;z:0);
   ZeroVec:Vec3 = (x:0;y:0;z:0);
   INFVec:Vec3=(x:INF*2;y:INF*2;z:INF*2);
   DefaultPosition:Vec3=(x:50.0; y:52.0; z:295.6);
   DefaultDirection:Vec3=(x:0.0; y:-0.042612; z:-1.0);

function VecAdd3(V1,V2,V3:Vec3):Vec3;
procedure VecWriteln(V:Vec3);
procedure WriteVec(v:Vec3);
function isINF(v:Vec3):boolean;

threadvar
   rnd:RandomRecord;

implementation

function isINF(v:Vec3):boolean;
begin
   if (v.x>INF) and (v.y>INF) and (v.z>INF) then result := true else result:=false;
end;

class function Vec3.new(x_,y_,z_:real):Vec3;static;inline;
begin
   result.x:=x_;result.y:=y_;result.z:=z_;
end;

function Vec3.Norm:Vec3;inline;
begin
   result:=self/sqrt(x*x+y*y+z*z);
end;

function Vec3.len:real;inline;
begin
   result:=sqrt(x*x+y*y+z*z);
end;

function Vec3.Dot(const V2 :Vec3):real;inline;//内積
begin
    result:=x*v2.x+y*v2.y+z*v2.z;
end;

function Vec3.Cross(const V2 :Vec3):Vec3;inline;//外積
begin
    result.x:=y * v2.z - v2.y * z;
    result.y:=z * v2.x - v2.z * x;
    result.z:=x * v2.y - v2.x * y;
end;

function Vec3.Mult(const V2:Vec3):Vec3;inline;
begin
    result.x:=x*V2.x;
    result.y:=y*V2.y;
    result.z:=z*V2.z;
end;

function Vec3.Neg:Vec3;
begin
    result.x:=-x;
    result.y:=-y;
    result.z:=-z;
end;

class function RayRecord.new(o_,d_:Vec3):RayRecord;
begin
   result.o:=o_;
   result.d:=d_;
 end;

function VecAdd3(V1,V2,V3:Vec3):Vec3;
begin
    result.x:=V1.x+V2.x+V3.x;
    result.y:=V1.y+V2.y+V3.y;
    result.z:=V1.z+V2.z+V3.z;
end;

procedure VecWriteln(V:Vec3);
begin
    writeln(v.x:7:3,':',v.y:7:3,':',v.z:7:3);
end;

procedure WriteVec(v:Vec3);
begin
   write('(',v.x:7:3,':',v.y:7:3,':',v.z:7:3,')');
end;

class operator Vec3.* (const v1: Vec3; const r: real): Vec3; inline;
begin
   result.x := v1.x * r;
   result.y := v1.y * r;
   result.z := v1.z * r;
end;

class operator Vec3./ (const v1: Vec3; const r: real): Vec3; inline;
begin
   result.x := v1.x / r;
   result.y := v1.y / r;
   result.z := v1.z / r;
end;

class operator Vec3.* (const v1, v2: Vec3): real; inline; // 内積
begin
   result := v1.x * v2.x + v1.y * v2.y + v1.z * v2.z;
end;

class operator Vec3./ (const v1, v2: Vec3): Vec3; inline; // 外積
begin
   result.x := v1.y * v2.z - v2.y * v1.z;
   result.y := v1.z * v2.x - v2.z * v1.x;
   result.z := v1.x * v2.y - v2.x * v1.y;
end;

class operator Vec3.+ (const v1, v2: Vec3): Vec3; inline;
begin
   result.x := v1.x + v2.x;
   result.y := v1.y + v2.y;
   result.z := v1.z + v2.z;
end;

class operator Vec3.- (const v1, v2: Vec3): Vec3; inline;
begin
   result.x := v1.x - v2.x;
   result.y := v1.y - v2.y;
   result.z := v1.z - v2.z;
end;

class operator Vec3.+ (const v1: Vec3; const r: real): Vec3; inline;
begin
   result.x := v1.x + r;
   result.y := v1.y + r;
   result.z := v1.z + r;
end;

class operator Vec3.- (const v1: Vec3; const r: real): Vec3; inline;
begin
   result.x := v1.x - r;
   result.y := v1.y - r;
   result.z := v1.z - r;
end;

function ClampVector(v:Vec3):Vec3;
begin
  result.r:=EnsureRange(v.r,0,1);
  result.g:=EnsureRange(v.g,0,1);
  result.b:=EnsureRange(v.b,0,1);
end;

function ColToWord(x:real):Word;inline;
begin
    result:=trunc(power(x,1/2.2)* MAX_WORD +0.5);
end;

function ColToRGB(v:Vec3):TFPColor;
begin
    result.red:=ColToWord(v.r);
    result.green:=ColToWord(v.g);
    result.blue:=ColToWord(v.b);
end;

function RGBtoColor(c:TFPColor):Vec3;inline;
begin
   result.r:=c.red*rev_MAX_WORD;
   result.g:=c.green*rev_MAX_WORD;
   result.b:=c.blue*rev_MAX_WORD;
end;

class function CamRecord.new(o_,d_:Vec3;w_,h_,samps_:integer):CamRecord;
begin
   result.o:=o_;
   result.d:=d_.norm;
   result.w:=w_;
   result.h:=h_;
   result.samps:=samps_;
   result.cx:=Vec3.new(result.w * 0.5135 / result.h, 0, 0);
   result.cy:= (result.cx/ result.d).norm* 0.5135;
   result.PlaneDist:=140;
end;

function CamRecord.GetRay(x,y,sx,sy:integer):RayRecord;
var
   r1,r2,dx,dy:real;
   dirct:Vec3;
begin
   r1 := 2 * rnd.random;
   if (r1 < 1) then dx := sqrt(r1) - 1 else dx := 1 - sqrt(2 - r1);
   r2 := 2 * rnd.random;
   if (r2 < 1) then dy := sqrt(r2) - 1 else dy := 1 - sqrt(2 - r2);
   dirct:= cy* (((sy + 0.5 + dy) / 2 + (h - y - 1)) / h - 0.5)
      +cx* (((sx + 0.5 + dx) / 2 + x) / w - 0.5)
      +d;
   dirct:=dirct.norm;
   result.o:= dirct* PlaneDist+o;
   result.d := dirct;
end;

procedure CamRecord.CamWrite;
var
   r:RayRecord;
begin
   write(' o=');VecWriteln(o);
   write(' d=');VecWriteln(d);
   write(' cx=');VecWriteln(cx);
   write(' cy=');VecWriteln(cy);
   writeln('===0,0==');
   r:=GetRay(0,0,0,0);
   write(' r.o=');VecWriteln(r.o);
   write(' r.d=');VecWriteln(r.d);
   writeln('===320,240==');
   r:=GetRay(320,240,0,0);
   write(' r.o=');VecWriteln(r.o);
   write(' r.d=');VecWriteln(r.d);   
end;


function Vec2.DirToUV(d:Vec3):Vec2;
var
  ClampedZ: Double;
begin
   d:=d.norm;
   Result.U := 0.5 - (ArcTan2(d.z, d.x) / (2.0 * Pi));

   // ArcSin に渡す値のクランプ (-1.0 ～ 1.0) で NaN を防止
   ClampedZ := EnsureRange(d.y, -1.0, 1.0);
   
   // 上が V=0 の場合
   Result.V := 0.5 - (ArcSin(ClampedZ) / Pi);
end;

constructor RandomRecord.Create(seed_: Cardinal);
var
   i: Integer;
begin
   FState[0] := seed_ and $FFFFFFFF;
   for i := 1 to N - 1 do begin
      FState[i] := 1812433253 * (FState[i - 1] xor (FState[i - 1] shr 30)) + i;
      FState[i] := FState[i] and $FFFFFFFF;
   end;
   FIndex := N;
end;

procedure RandomRecord.Twist;
var
   i: Integer;
   y: Cardinal;
begin
   for i := 0 to N - 1 do  begin
      y := (FState[i] and UPPER_MASK) or (FState[(i + 1) mod N] and LOWER_MASK);
      FState[i] := FState[(i + 156) mod N] xor (y shr 1);
      if (y and 1) <> 0 then FState[i] := FState[i] xor MATRIX_A;
   end;
   FIndex := 0;
end;

function RandomRecord.Random: real;inline;
var
   y: Cardinal;
begin
   if FIndex >= N then Twist;

   y := FState[FIndex];
   Inc(FIndex);

   // 攪拌（Tempering）処理
   y := y xor (y shr 11);   y := y xor ((y shl 7) and $9D2C5680);
   y := y xor ((y shl 15) and $EFC60000);   y := y xor (y shr 18);

   // [0, 1) の範囲の浮動小数点数に変換
   Result := y / 4294967296.0;
end;


begin
end.
   
