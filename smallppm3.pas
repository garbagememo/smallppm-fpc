program smallppm;
{$MODE objfpc}
{$INLINE ON}

uses classes,math,uVect,uBMP,SysUtils,getopts;//WriteBMPにCLAMPとかも入れる
const
   ALPHA                          = 0.7;
   PhotonBallRadius               = 3;
   PhotonBallRadiusPlus           = PhotonBallRadius+0.1;
   primes:array[0..60] of integer = (
      2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,
      83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,
      191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283
  );
  inf=1e20;

function rev(i,p:integer):integer;inline;
begin
  if i=0 then result:=i else result:=p-i; 
end;

function hal(b,j:integer):real;inline;
var
   p:integer;
   h,f,fct:real;
begin
   p := primes[b]; 
   h := 0; f := 1/p; fct := f;
   while j > 0 do begin
      h :=h+rev(j mod p, p) * fct; j :=j div p; fct:=fct * f;
   end;
   result:=h;
end;

type
   AABBRecord=Record
      vMin,vMax:VecRecord;
   end;

procedure AABBFit(var AB:AABBRecord;p:VecRecord);inline;
begin
  IF p.x<AB.vMin.x THEN AB.vMin.x:=p.x; // min
  IF p.y<AB.vMin.y THEN AB.vMin.y:=p.y; // min
  IF p.z<AB.vMin.z THEN AB.vMin.z:=p.z; // min
  AB.vMax.x:=MAX(p.x, AB.vMax.x);
  AB.vMax.y:=MAX(p.y, AB.vMax.y);
  AB.vMax.z:=MAX(p.z, AB.vMax.z);
end;

procedure AABBReset(var AB:AABBRecord);inline;
begin
  AB.vMin.x:=INF;AB.vMax.x:=-INF;
  AB.vMin.y:=INF;AB.vMax.y:=-INF;
  AB.vMin.z:=INF;AB.vMax.z:=-INF;
end;

type
  HPointRecord=record
    f,pos,nrm,flux:VecRecord;
    r2:real;
    n:LongWord;//n=N/ALPHA
    pix:integer;
  end;
  pHPoint=^HPointRecord;

  pList=^ListRecord;
  ListRecord=Record
    id:pHPoint;
    next:pList;    
  end;

function ListAdd(i:pHpoint;h:pList):pList;
var
  p:pList;
begin
  New(p);
  p^.id:=i;
  p^.next:=h;
  result:=p;
end;

var
  num_hash,pixel_index,num_photon:LongWord;
  hash_s:real;
  hash_grid:array of pList;
  hitpoints:pList;
  hpbbox:AABBRecord;

function hash(ix,iy,iz:integer):LongWord;inline;
var 
  LW:Longword;
begin
  LW:=((ix*73856093)xor(iy*19349663)xor(iz*83492791)) ;
  LW:=LW mod num_hash;
  result:=LW;
end;

procedure build_hash_grid(w,h:integer) ;
var
  lst:pList;
  hp:pHpoint;
  ssize,BMin,BMax:VecRecord;
  irad:real;
  vphoton:integer;
  i,iz,izs,ize,iy,iys,iye,ix,ixs,ixe:integer;
  hv:LongWord;
begin
   // find the bounding box of all the measurement points
    AABBReset(hpbbox);
    lst := hitpoints;
    while lst <>Nil do begin
        hp:=lst^.id; 
        lst:=lst^.next; 
        AABBFit(hpbbox,hp^.pos);
    END;

    // heuristic for initial radius
    ssize := hpbbox.vMax - hpbbox.vMin;
    irad := ((ssize.x + ssize.y + ssize.z) / 3 ) / ((w + h) / 2 ) * 2.0;

    // determine hash table size
    // we now find the bounding box of all the measurement points inflated by the initial radius
    AABBReset(hpbbox); 
    lst := hitpoints; 
    vphoton := 0; 
    while lst <> nil do begin
        hp := lst^.id; 
        lst := lst^.next;
        hp^.r2:=irad *irad; 
        hp^.n := 0; 
        hp^.flux := ZeroVec;
        inc(vPhoton);
        AABBFit(hpbbox,hp^.pos-irad);
        AABBFit(hpbbox,hp^.pos+irad);
    end;
writeln('pass AABBFit');

    // make each grid cell two times larger than the initial radius
    hash_s:=1.0/(irad*2.0); 
    num_hash := vphoton; 

    // build the hash table
    SetLength(hash_grid,(num_hash+1)*Sizeof(pHPoint) ); //=new List*[num_hash];
Writeln('Pass SetLength');
    for i:=0 to num_hash do hash_grid[i]:=Nil;
Writeln('Hash nil done');
    lst := hitpoints; 
    while lst <> nil do begin
        hp := lst^.id; 
        lst := lst^.next;
        BMin := ((hp^.pos - irad) - hpbbox.vMin) * hash_s;
        BMax := ((hp^.pos + irad) - hpbbox.vMin) * hash_s;
        izs:=abs(trunc(BMin.z));ize:=abs(trunc(BMax.z));
        iys:=abs(trunc(BMin.y));iye:=abs(trunc(BMax.y));
        ixs:=abs(trunc(BMin.x));ixe:=abs(trunc(BMax.x));
        for iz:=izs to ize do begin
           for iy:=iys to iye do begin
              for ix:=ixs to ixe do begin
                  hv:=hash(ix,iy,iz);
                  hash_grid[hv]:=ListAdd(hp,hash_grid[hv]);
              end;//ix
           end;//iy
        end;//iz
    end;//while 
end;


TYPE
  SphereClass=Class
    rad:real;
    p,c:VecRecord;
    refl:RefType;
    constructor Create(r_:real;p_,c_:VecRecord;re_:RefType);
    function intersect(var r:RayRecord):real;
  END;
  constructor SphereClass.Create(r_:real;p_,c_:VecRecord;re_:RefType);
  begin
    rad:=r_;p:=p_;c:=c_;refl:=re_;
  end;
  function SphereClass.intersect(var r:RayRecord):real;
  var
    op:VecRecord;
    t,b,det:real;
  begin
    op:=p-r.o; 
    b:=VecDot(op,r.d); 
    det:=b*b-VecDot(op,op)+rad*rad;
    IF det < 0 THEN begin
       result:= INF ;exit;
    end
    else begin 
       det:=sqrt(det);
       t:=b-det;
       IF t>1e-4 then 
           result:=t
       else begin
           t:=b+det;
           IF t>1e-4 then result:=t else t:=INF;
           result:=t;
       end;
    end;
  end;

var
  sph:TList;
  RLight,GLight,BLight : SphereClass;

procedure InitScene;
begin
  sph:=TList.Create;
  sph.add( SphereClass.Create(1e5, CreateVec( 1e5+1,40.8,81.6), CreateVec(0.75,0.25,0.25),DIFF) );//Left
  sph.add( SphereClass.Create(1e5, CreateVec(-1e5+99,40.8,81.6),CreateVec(0.25,0.25,0.75),DIFF) );//Right
  sph.add( SphereClass.Create(1e5, CreateVec(50,40.8, 1e5),     CreateVec(0.75,0.75,0.75),DIFF) );//Back
  sph.add( SphereClass.Create(1e5, CreateVec(50,40.8,-1e5+170), CreateVec(0,0,0),      DIFF) );//Front
  sph.add( SphereClass.Create(1e5, CreateVec(50, 1e5, 81.6),    CreateVec(0.75,0.75,0.75),DIFF) );//Bottomm
  sph.add( SphereClass.Create(1e5, CreateVec(50,-1e5+81.6,81.6),CreateVec(0.75,0.75,0.75),DIFF) );//Top
  sph.add( SphereClass.Create(16.5,CreateVec(27,16.5,47),       CreateVec(1,1,1)*0.999, SPEC) );//Mirror
  sph.add( SphereClass.Create(16.5,CreateVec(73,16.5,88),       CreateVec(1,1,1)*0.999, REFR) );//Glass
  sph.add( SphereClass.Create(8.5, CreateVec(50,8.5,60),        CreateVec(1,1,1)*0.999, DIFF) );//Middle
   RLight:=SphereClass.Create(PhotonBallRadius,CreateVec(50   ,60,      85)   ,CreateVec(0.5,  1,  1)*0.999,DIFF);//Light Ball-R
   GLight:=SphereClass.Create(PhotonBallRadius,CreateVec(50+20,60,85-17.32*2),CreateVec(  1,0.5,  1)*0.999,DIFF);//Light Ball-G
   BLight:=SphereClass.Create(PhotonBallRadius,CreateVec(50-20,60,85-17.32*2),CreateVec(  1,  1,0.5)*0.999,DIFF);//Light Ball-B
   sph.add(RLight);sph.add(GLight);sph.add(BLight);        
end;

// tone mapping and gamma correction
function toInt(x:real):integer;
begin
    result:=trunc(power( 1-exp(-x) ,1/2.2)*255+0.5); 
end;
function ToByteColor(x:real):byte;
begin
   result:=trunc(power(1-exp(-x),1/2.2)*255+0.5); 
end;

function ColToRGB(c:VecRecord):rgbColor;
begin
  result.r:=ToByteColor(c.x);
  result.g:=ToByteColor(c.y);
  result.b:=ToByteColor(c.z);
end;

// find the closet interection
function intersect(r:RayRecord;var t:real;var id:integer):boolean;
var
  n,i:integer;
  d:real;
begin
    n := sph.count; 
    t := inf;
    for i:=0 to n-1 do begin
        d:=SphereClass(sph[i]).intersect(r);
        if d<t THEN BEGIN
            t:=d;
            id:=i;
        end;
    end;
    IF t<INF THEN Result:=TRUE ELSE Result:=FALSE;
end;

// generate a photon ray from the point light source with QMC
procedure genp(var pr:RayRecord;var f:VecRecord;i:integer);
var
    p,t,st:real;
begin
    f := CreateVec(2500,2500,2500)*(PI*4.0); // flux
    p:=2.0*PI*hal(0,i);t:=2.0*arccos(sqrt(1.0-hal(1,i)));
    st:=sin(t);
    pr.d:=CreateVec(cos(p)*st,cos(t),sin(p)*st);
    pr.o:=CreateVec(50,60,85);
end;
procedure genp2(var pr:RayRecord;var f:VecRecord;i:integer);
var
    p,t,st:real;
begin
    f := CreateVec(2500,2500,2500)*(PI*4.0); // flux
    p:=2.0*PI*hal(0,i);t:=2.0*arccos(sqrt(1.0-hal(1,i)));
    st:=sin(t);
    pr.d:=CreateVec(cos(p)*st,cos(t),sin(p)*st);
    pr.o:=CreateVec(50,60,85);
end;

procedure GenPhoton(var pr : RayRecord;var f:VecRecord;i:integer;LightCount:integer);
var
    p,t,st:real;
begin
   case LightCount of
     1 : f:=CreateVec( 500,1500,1500);
     2 : f:=CreateVec(1500, 500,1500);
     3 : f:=CreateVec(1500,1500, 500);
   end;
   f := CreateVec(1500,1500,1500)*(PI*4.0); // flux
   p:=2.0*PI*hal(0,i);t:=2.0*arccos(sqrt(1.0-hal(1,i)));
   st:=sin(t);
   pr.d:=CreateVec(cos(p)*st,cos(t),sin(p)*st);
   Case LightCount of
     1 : pr.o:=RLight.p;
     2 : pr.o:=GLight.p;
     3 : pr.o:=BLight.p;
   end;
   
//   pr.o:=CreateVec(50,60,85)+VecNorm(pr.d)*PhotonBallRadiusPlus;
  // IF hal(2,i)>0.5 THEN pr.d:=pr.d*(-1);
end;


procedure trace(r:RayRecord;dpt:integer;m:boolean;fl,adj:VecRecord;i:integer);
var
  t,p:real;
  id:integer;
  d3:integer;
  obj:SphereClass;
  x,n,f,nl:VecRecord;
  r1,r2,r2s:real;
  w,u,v,d:VecRecord;
  hp:pHPoint;
  hh:VecRecord;
  ix,iy,iz:integer;
  pL:pList;
  g:real;
  lr,rr:RayRecord;
  into:boolean;
  nnt,nc,nt,ddn,cos2t,a,b,R0,c,Re,Q:real;
  td,fa:VecRecord;
begin
    inc(dpt);
    IF (intersect(r,t,id)=FALSE) or (dpt>=20) THEN EXIT;
 
    d3:=dpt*3;
    obj := SphereClass(sph[id]); 
    x:=r.o+r.d*t; n:=VecNorm(x-obj.p); f:=obj.c;
    IF VecDot(n,r.d)<0 THEN nl:=n else nl:=n*-1;
    IF (f.x>f.y)and(f.x>f.z) THEN
      p:=f.x
    ELSE IF f.y>f.z THEN 
      p:=f.y
    ELSE
      p:=f.z;

    case obj.refl of
    DIFF:BEGIN
        // Lambertian

        // use QMC to sample the next direction
        r1:=2.*PI*hal(d3-1,i);r2:=hal(d3+0,i);r2s:=sqrt(r2);
        w:=nl;
        IF abs(w.x)>0.1 THEN
           u:=CreateVec(0,1,0) 
        ELSE BEGIN
           u:=VecNorm( VecCross(CreateVec(1,0,0),w ) );
        END;
        v:=VecCross(w,u);d := VecNorm(u*cos(r1)*r2s + v*sin(r1)*r2s + w*sqrt(1-r2));

        if m THEN BEGIN
            // eye ray
            // store the measurment point
            New(hp); 
            hp^.f:=VecMul(f,adj); 
            hp^.pos:=x;
            hp^.nrm:=n; 
            hp^.pix := pixel_index; 
            hitpoints := ListAdd(hp, hitpoints);
        END 
        ELSE BEGIN 
            // photon ray
            // find neighboring measurement points and accumulate flux via progressive density estimation
            hh := (x-hpbbox.vMin) * hash_s;
            ix := abs(trunc(hh.x)); iy := abs(trunc(hh.y)); iz := abs(trunc(hh.z));
            // strictly speaking, we should use #pragma omp critical here.
            // it usually works without an artifact due to the fact that photons are 
            // rarely accumulated to the same measurement points at the same time (especially with QMC).
            // it is also significantly faster.
            BEGIN
                pL := hash_grid[hash(ix, iy, iz)]; 
                while (pL <> Nil) DO BEGIN
                    hp := pL^.id; 
                    pL:= pL^.next; 
                    v := hp^.pos - x;
                    // check normals to be closer than 90 degree (avoids some edge brightning)
                    if (VecDot(hp^.nrm,n) > 1e-3) and (VecDot(v,v) <= hp^.r2) THEN BEGIN
                        // unlike N in the paper, hitpoint->n stores "N / ALPHA" to make it an integer value
                        g := (hp^.n*ALPHA+ALPHA) / (hp^.n*ALPHA+1.0);
                        hp^.r2:=hp^.r2*g; 
                        inc(hp^.n);
                        hp^.flux:=(hp^.flux+VecMul(hp^.f,fl)*(1.0/PI))*g;
                    END;
                END;
            END;
            IF hal(d3+1,i)<p THEN trace(CreateRay(x,d),dpt,m,VecMul(f,fl)*(1/p),adj,i);
        END;
    END;(*DIFF*)
    SPEC:BEGIN
     // mirror
       trace(CreateRay(x, r.d-n*2.0*VecDot(n,r.d)), dpt, m, VecMul(f,fl), VecMul(f,adj),i);

    END;(*SPEC*)
    REFR:BEGIN
        // glass
        lr:=CreateRay(x,r.d-n*2.0*VecDot(n,r.d)); 
        into := (VecDot(n,nl)>0.0);
        nc := 1.0; nt:=1.5;
        if into then 
           nnt:=nc/nt
        else 
           nnt:=nt/nc;
        ddn := VecDot(r.d,nl);
        cos2t:=1-nnt*nnt*(1-ddn*ddn);

        // total internal reflection
        if cos2t<0 then begin
           trace(lr,dpt,m,fl,adj,i);
           exit;
        end;

        IF into then Q:=1 ELSE Q:=-1;
        td := VecNorm( r.d*nnt - n*(Q*( ddn*nnt+sqrt(cos2t) )) );
        IF into then Q:=-ddn else Q:=VecDot(td,n);
        a:=nt-nc; b:=nt+nc; R0:=a*a/(b*b); c := 1-Q;
        Re:=R0+(1-R0)*c*c*c*c*c; P:=Re; rr:=CreateRay(x,td); fa:=VecMul(f,adj);
        if m THEN BEGIN
            // eye ray (trace both rays)
            trace(lr,dpt,m,fl,fa*Re,i);
            trace(rr,dpt,m,fl,fa*(1.0-Re),i);
        END
        ELSE BEGIN
            // photon ray (pick one via Russian roulette)
            IF hal(d3-1,i)<P THEN 
               trace(lr,dpt,m,fl,fa,i)
            ELSE
               trace(rr,dpt,m,fl,fa,i);
        END;
    END(*REFR*)
    END;(*CASE*)
END;

procedure debuginfo(m:boolean);
var
  ix,iy,iz:integer;
  LW:LongWord;
begin
  num_hash:=1000;
  ix:=100; iy:=1000;iz:=10;
  writeln(' ix=',ix,' iy=',iy,' iz=',iz);
  writeln(' Hash Midium value=',(ix*73856093)xor(iy*19349663)xor(iz*83492791));
  writeln(' hal(1,2)=',hal(1,2));
  writeln('Hash Value=',hash(ix,iy,iz) );
end;


var
  w,h,samps,y,x	: integer;
   i,j,m,n	: integer;
   cam,r		: RayRecord;
   d,cx,cy,vw,f	: VecRecord;
   c		: array of VecRecord;
   BMPIO	: BMPIOClass;
   p		: real;
   lst		: pList;
   hp		: pHPoint;
   T1,T2		: TDateTime;
   HH,MM,SS,MS	: WORD;
   co		: char;
   ArgInt	: integer;
   ArgFN,FN		: String;
BEGIN
    hitpoints:=Nil;
    InitScene;
   FN:='out.bmp';
   samps:=1000;
    // samps * 1000 photon paths will be traced
    w:=1024;    h:=768;
 //   w:=320;h:=240;
  co:=#0;
  repeat
    co:=getopt('o:s:w:');

    case co of
      'o' : BEGIN
         ArgFN:=OptArg;
         IF ArgFN<>'' THEN FN:=ArgFN;
         writeln ('Output FileName =',FN);
      END;
      's' : BEGIN
        ArgInt:=StrToInt(OptArg);
        samps:=ArgInt;
        writeln('samples =',ArgInt);
      END;
      'w' : BEGIN
         ArgInt:=StrToInt(OptArg);
         w:=ArgInt;h:=w *3 div 4;
         writeln('w=',w,' ,h=',h);
      END;
      '?',':' : BEGIN
         writeln(' -o [finename] output filename');
         writeln(' -s [samps] sampling count');
         writeln(' -w [width] screen width pixel');
      END;
    end; { case }
  until co=endofoptions;
   
    BMPIO:=BMPIOClass.Create(w,h);

  T1:=Time;
  Writeln ('The time is : ',TimeToStr(Time));

    // trace eye rays and store measurement points
    cam:=CreateRay(CreateVec(50,48,295.6), VecNorm(CreateVec(0,-0.042612,-1)) );
    cx:=CreateVec(w*0.5135/h,0,0); cy:=VecNorm(VecCross(cx,cam.d))*0.5135;
    
    SetLength(c,w*h);

    for y:=0 to h-1 do begin
       IF y mod 20 =0 then 
        writeln(' HitPointPass=',FloatToStrF(100*y/(h-1),ffFixed,2,2) );
        
        for x:=0 to w-1 do begin
            pixel_index := x + y * w;
            d := cx * ((x + 0.5) / w - 0.5) + cy * (-(y + 0.5) / h + 0.5)+cam.d;
            trace(CreateRay(cam.o + d * 140, VecNorm(d) ), 
                  0,
                  true,
                  CreateVec(0,0,0),
                  CreateVec(1, 1, 1),
                  0);
        end;
    end;
    
writeln(' Before Hash');  
    // build the hash table over the measurement points
    build_hash_grid(w,h); 
    
    // trace photon rays with multi-threading
    num_photon:=samps; 
    vw:=CreateVec(1,1,1);
//    #pragma omp parallel for schedule(dynamic, 1)
    for i:=0 to num_photon-1 do begin
        p:=100*(i+1)/num_photon;
        m:=1000*i;
       IF i mod 100 =0 THEN Writeln(' %=',FloatToStrf(p,ffFixed,2,1));
        for j:=0 to 1000-1 do begin
//            genp(r,f,m+j);
           GenPhoton(r,f,m+j,1);//red
            trace(r,0,false,f,vw,m+j);
           GenPhoton(r,f,m+j,2);//green
            trace(r,0,false,f,vw,m+j);
           GenPhoton(r,f,m+j,3);//blue
            trace(r,0,false,f,vw,m+j);
        end;
    end;

    // density estimation
    lst:=hitpoints; 
    while lst<>nil do begin
        hp:=lst^.id;
        lst:=lst^.next;
        i:=hp^.pix;
        c[i]:=c[i]+hp^.flux*(1.0/(PI*hp^.r2*num_photon*1000.0));
    end;

  T2:=Time-T1;
  DecodeTime(T2,HH,MM,SS,MS);
  Writeln ('The time is : ',HH,'h:',MM,'min:',SS,'sec');


    // save the image after tone mapping and gamma correction
    for y:=0 to h-1 do begin
      for x:=0 to w-1 do begin
        BMPIO.SetPixel(x,h-1-y,ColToRGB(c[x+y*w]) );
      end;
    end;
    BMPIO.WriteBMPFile(FN);
end.

(*$Log: smallppm_exp.pas,v $*)
(*Revision 1.3  2018/02/04 12:17:57  average*)
(*BMP Write Bug Fix*)
