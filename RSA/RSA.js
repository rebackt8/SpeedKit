function HtoB64(h){return btoa(String.fromCharCode.apply(this,h.match(/.{2}/g).map(function(v){return parseInt(v,16)})))}
function B64toH(b){return atob(b).split("").map(function(v){return v.charCodeAt(0).toString(16)}).join("")}

function RSA(s,k){
	if([512,1024,2048,4096].indexOf(s)==-1)return;
	this.SIZE=s;
	
	k?this.parseKey(k):this.generate(s);
	this.PUBLIC="-----BEGIN PUBLIC KEY-----\n"+this.getPublicBaseKey().match(/(.{1,64})( +|$\n?)|(.{1,64})/g).join('\n')+"\n-----END PUBLIC KEY-----";
}

RSA.prototype.doPublic = function(x){return x.modPowInt(65537, this.n);}

RSA.prototype.encrypt = function(text) {
	var c = this.doPublic(pkcs1pad2(text, this.n.bitLength() + 7 >> 3));
	var h = c.toString(16);
	if ((h.length & 1) == 0) return HtoB64(h); else return HtoB64("0" + h);
}


RSA.prototype.doPrivate = function(x) {
	if (this.p == null || this.q == null) return x.modPow(this.d, this.n);
	var xp = x.mod(this.p).modPow(this.dmp1, this.p);
	var xq = x.mod(this.q).modPow(this.dmq1, this.q);
	while (xp.compareTo(xq) < 0) xp = xp.add(this.p);
	return xp.subtract(xq).multiply(this.coeff).mod(this.p).multiply(this.q).add(xq);
}

RSA.prototype.decrypt = function(ctext) {
	var c = new BigInteger(b64tohex(ctext), 16);
	var m = this.doPrivate(c);
	var b=m.toByteArray();
	return String.fromCharCode.apply(null,b.slice(b.indexOf(0)+1))
}



RSA.prototype.generate = function(B){
	this.q = new BigInteger(B/2, 1, this.SIZE);
		var q1 = this.q.sub1();

	this.p = new BigInteger(B/2, 1, this.SIZE);
		var p1_d = this.p.sub1_d_SIZE(this.SIZE,q1);
		var p1_dmp1 = this.p.sub1_SIZE(this.SIZE);
		
		this.n = this.p.multiply(this.q);
		//this.d = makeD(p1_d.multiply2(q1));
		this.d = makeD(p1_d);
		this.dmp1 = this.d.makeDMP1(p1_dmp1,this.SIZE);
		this.dmq1 = this.d.mod(q1);
		this.coeff = this.q.modInverse(this.p);
}

RSA.prototype.parseKey = function(k){
	for(var m=/-----BEGIN [^-]+-----([A-Za-z0-9+\/=\s]+)-----END [^-]+-----|begin-base64[^\n]+\n([A-Za-z0-9+\/=\s]+)====/.exec(k),l=0,d=atob(m[1]),c=[];l<d.length;l++)c.push(d.charCodeAt(l));var P=0,n=c[1],m=n&127,d=m===n?0:m;P+=c[d+3]+d+4;P+=(c[P]==3)+d+d+5;var i=P+d+1,e=i+c[i-1];while(d-->1)e|=c[++P]<<8;
	
	for(var s="",f=function(x){return (x&15).toString(16)};i<e;++i) s+=f(c[i]>>4)+f(c[i]);
	
	this.n = new BigInteger(s,16);
}

RSA.prototype.getPublicBaseKey = function(){
	var x,y;
	switch(this.SIZE){
		case 512: x="305b",y="034a0030470240"; break;
		case 1024: x="30819e",y="03818c00308188028180"; break;
		case 2048: x="30820121",y="0382010e003082010902820100"; break;
		case 4096: x="30820221",y="0382020e003082020902820200"; break;
		default: return "";
	}
	return HtoB64(x+"300d06092a864886f70d0101010500"+y+this.n.toString(16)+"0203010001");
}

var dbits;
var canary = 0xdeadbeefcafe;
var j_lm = (canary & 16777215) == 15715070;
function BigInteger(a, b, Z){
	if(Z)this.fromMagic(Z);

	if (a != null) if ("number" == typeof a) this.fromNumber(a, b); else if (b == null && "string" != typeof a) this.fromString(a, 256); else this.fromString(a, b);
}
function nbi() {
	return new BigInteger(null);
}

BigInteger.prototype.am = function(i, x, w, j, c, n) {
	var xl = x & 16383, xh = x >> 14;
	while (--n >= 0) {
		var l = this[i] & 16383;
		var h = this[i++] >> 14;
		var m = xh * l + h * xl;
		l = xl * l + ((m & 16383) << 14) + w[j] + c;
		c = (l >> 28) + (m >> 14) + xh * h;
		w[j++] = l & 268435455;
	}
	return c;
}
dbits = 28;

BigInteger.prototype.DB = 28;
BigInteger.prototype.DM = 268435455;
BigInteger.prototype.DV = 268435456;
var BI_FP = 52;
BigInteger.prototype.FV = Math.pow(2, 52);
BigInteger.prototype.F1 = 24;
BigInteger.prototype.F2 = 4;
var BI_RM = "0123456789abcdefghijklmnopqrstuvwxyz";
var BI_RC = new Array();
var rr, vv;
rr = "0".charCodeAt(0);
for (vv = 0; vv <= 9; ++vv) BI_RC[rr++] = vv;
rr = "a".charCodeAt(0);
for (vv = 10; vv < 36; ++vv) BI_RC[rr++] = vv;
rr = "A".charCodeAt(0);
for (vv = 10; vv < 36; ++vv) BI_RC[rr++] = vv;
function int2char(n) {
	return BI_RM.charAt(n);
}
function intAt(s, i) {
	var c = BI_RC[s.charCodeAt(i)];
	return c == null ? -1 : c;
}
function bnpCopyTo(r) {
	for (var i = this.t - 1; i >= 0; --i) r[i] = this[i];
	r.t = this.t;
	r.s = this.s;
}
function bnpFromInt(x) {
	this.t = 1;
	this.s = x < 0 ? -1 : 0;
	if (x > 0) this[0] = x; else if (x < -1) this[0] = x + this.DV; else this.t = 0;
}
function nbv(i) {
	var r = nbi();
	r.fromInt(i);
	return r;
}
function bnpFromString(s, b) {
	var k;
	if (b == 16) k = 4; else if (b == 8) k = 3; else if (b == 256) k = 8; else if (b == 2) k = 1; else if (b == 32) k = 5; else if (b == 4) k = 2; else {
		this.fromRadix(s, b);
		return;
	}
	this.t = 0;
	this.s = 0;
	var i = s.length, mi = false, sh = 0;
	while (--i >= 0) {
		var x = k == 8 ? s[i] & 255 : intAt(s, i);
		if (x < 0) {
			if (s.charAt(i) == "-") mi = true;
			continue;
		}
		mi = false;
		if (sh == 0) this[this.t++] = x; else if (sh + k > this.DB) {
			this[this.t - 1] |= (x & (1 << this.DB - sh) - 1) << sh;
			this[this.t++] = x >> this.DB - sh;
		} else this[this.t - 1] |= x << sh;
		sh += k;
		if (sh >= this.DB) sh -= this.DB;
	}
	if (k == 8 && (s[0] & 128) != 0) {
		this.s = -1;
		if (sh > 0) this[this.t - 1] |= (1 << this.DB - sh) - 1 << sh;
	}
	this.clamp();
	if (mi) BigInteger.ZERO.subTo(this, this);
}
function bnpClamp() {
	var c = this.s & this.DM;
	while (this.t > 0 && this[this.t - 1] == c) --this.t;
}
function bnToString(b) {
	if (this.s < 0) return "-" + this.negate().toString(b);
	var k;
	if (b == 16) k = 4; else if (b == 8) k = 3; else if (b == 2) k = 1; else if (b == 32) k = 5; else if (b == 4) k = 2; else return this.toRadix(b);
	var km = (1 << k) - 1, d, m = false, r = "", i = this.t;
	var p = this.DB - i * this.DB % k;
	if (i-- > 0) {
		if (p < this.DB && (d = this[i] >> p) > 0) {
			m = true;
			r = int2char(d);
		}
		while (i >= 0) {
			if (p < k) {
				d = (this[i] & (1 << p) - 1) << k - p;
				d |= this[--i] >> (p += this.DB - k);
			} else {
				d = this[i] >> (p -= k) & km;
				if (p <= 0) {
					p += this.DB;
					--i;
				}
			}
			if (d > 0) m = true;
			if (m) r += int2char(d);
		}
	}
	return m ? r : "0";
}


function bnCompareTo(a) {
	var r = this.s - a.s;
	if (r != 0) return r;
	var i = this.t;
	r = i - a.t;
	if (r != 0) return this.s < 0 ? -r : r;
	while (--i >= 0) if ((r = this[i] - a[i]) != 0) return r;
	return 0;
}
function nbits(x) {
	var r = 1, t;
	if ((t = x >>> 16) != 0) {
		x = t;
		r += 16;
	}
	if ((t = x >> 8) != 0) {
		x = t;
		r += 8;
	}
	if ((t = x >> 4) != 0) {
		x = t;
		r += 4;
	}
	if ((t = x >> 2) != 0) {
		x = t;
		r += 2;
	}
	if ((t = x >> 1) != 0) {
		x = t;
		r += 1;
	}
	return r;
}
function bnBitLength() {
	if (this.t <= 0) return 0;
	return this.DB * (this.t - 1) + nbits(this[this.t - 1] ^ this.s & this.DM);
}
function bnpDLShiftTo(n, r) {
	var i;
	for (i = this.t - 1; i >= 0; --i) r[i + n] = this[i];
	for (i = n - 1; i >= 0; --i) r[i] = 0;
	r.t = this.t + n;
	r.s = this.s;
}
function bnpDRShiftTo(n, r) {
	for (var i = n; i < this.t; ++i) r[i - n] = this[i];
	r.t = Math.max(this.t - n, 0);
	r.s = this.s;
}
function bnpLShiftTo(n, r) {
	var bs = n % this.DB;
	var cbs = this.DB - bs;
	var bm = (1 << cbs) - 1;
	var ds = Math.floor(n / this.DB), c = this.s << bs & this.DM, i;
	for (i = this.t - 1; i >= 0; --i) {
		r[i + ds + 1] = this[i] >> cbs | c;
		c = (this[i] & bm) << bs;
	}
	for (i = ds - 1; i >= 0; --i) r[i] = 0;
	r[ds] = c;
	r.t = this.t + ds + 1;
	r.s = this.s;
	r.clamp();
}
function bnpRShiftTo(n, r) {
	r.s = this.s;
	var ds = Math.floor(n / this.DB);
	if (ds >= this.t) {
		r.t = 0;
		return;
	}
	var bs = n % this.DB;
	var cbs = this.DB - bs;
	var bm = (1 << bs) - 1;
	r[0] = this[ds] >> bs;
	for (var i = ds + 1; i < this.t; ++i) {
		r[i - ds - 1] |= (this[i] & bm) << cbs;
		r[i - ds] = this[i] >> bs;
	}
	if (bs > 0) r[this.t - ds - 1] |= (this.s & bm) << cbs;
	r.t = this.t - ds;
	r.clamp();
}
function bnpSubTo(a, r) {
	var i = 0, c = 0, m = Math.min(a.t, this.t);
	while (i < m) {
		c += this[i] - a[i];
		r[i++] = c & this.DM;
		c >>= this.DB;
	}
	if (a.t < this.t) {
		c -= a.s;
		while (i < this.t) {
			c += this[i];
			r[i++] = c & this.DM;
			c >>= this.DB;
		}
		c += this.s;
	} else {
		c += this.s;
		while (i < a.t) {
			c -= a[i];
			r[i++] = c & this.DM;
			c >>= this.DB;
		}
		c -= a.s;
	}
	r.s = c < 0 ? -1 : 0;
	if (c < -1) r[i++] = this.DV + c; else if (c > 0) r[i++] = c;
	r.t = i;
	r.clamp();
}
function bnpMultiplyTo(a, r) {
	var x = this.abs(), y = a.abs();
	var i = x.t;
	r.t = i + y.t;
	while (--i >= 0) r[i] = 0;
	for (i = 0; i < y.t; ++i) r[i + x.t] = x.am(0, y[i], r, i, 0, x.t);
	r.s = 0;
	r.clamp();
	if (this.s != a.s) BigInteger.ZERO.subTo(r, r);
}
function bnpSquareTo(r) {
	var x = this.abs();
	var i = r.t = 2 * x.t;
	while (--i >= 0) r[i] = 0;
	for (i = 0; i < x.t - 1; ++i) {
		var c = x.am(i, x[i], r, 2 * i, 0, 1);
		if ((r[i + x.t] += x.am(i + 1, 2 * x[i], r, 2 * i + 1, c, x.t - i - 1)) >= x.DV) {
			r[i + x.t] -= x.DV;
			r[i + x.t + 1] = 1;
		}
	}
	if (r.t > 0) r[r.t - 1] += x.am(i, x[i], r, 2 * i, 0, 1);
	r.s = 0;
	r.clamp();
}
function bnpDivRemTo(m, q, r) {
	var pm = m.abs();
	if (pm.t <= 0) return;
	var pt = this.abs();
	if (pt.t < pm.t) {
		if (q != null) q.fromInt(0);
		if (r != null) this.copyTo(r);
		return;
	}
	if (r == null) r = nbi();
	var y = nbi(), ts = this.s, ms = m.s;
	var nsh = this.DB - nbits(pm[pm.t - 1]);
	if (nsh > 0) {
		pm.lShiftTo(nsh, y);
		pt.lShiftTo(nsh, r);
	} else {
		pm.copyTo(y);
		pt.copyTo(r);
	}
	var ys = y.t;
	var y0 = y[ys - 1];
	if (y0 == 0) return;
	var yt = y0 * (1 << this.F1) + (ys > 1 ? y[ys - 2] >> this.F2 : 0);
	var d1 = this.FV / yt, d2 = (1 << this.F1) / yt, e = 1 << this.F2;
	var i = r.t, j = i - ys, t = q == null ? nbi() : q;
	y.dlShiftTo(j, t);
	if (r.compareTo(t) >= 0) {
		r[r.t++] = 1;
		r.subTo(t, r);
	}
	BigInteger.ONE.dlShiftTo(ys, t);
	t.subTo(y, y);
	while (y.t < ys) y[y.t++] = 0;
	while (--j >= 0) {
		var qd = r[--i] == y0 ? this.DM : Math.floor(r[i] * d1 + (r[i - 1] + e) * d2);
		if ((r[i] += y.am(0, qd, r, j, 0, ys)) < qd) {
			y.dlShiftTo(j, t);
			r.subTo(t, r);
			while (r[i] < --qd) r.subTo(t, r);
		}
	}
	if (q != null) {
		r.drShiftTo(ys, q);
		if (ts != ms) BigInteger.ZERO.subTo(q, q);
	}
	r.t = ys;
	r.clamp();
	if (nsh > 0) r.rShiftTo(nsh, r);
	if (ts < 0) BigInteger.ZERO.subTo(r, r);
}

function bnMod(a) {
	var r = nbi();
	this.abs().divRemTo(a, null, r);
	if (this.s < 0 && r.compareTo(BigInteger.ZERO) > 0) a.subTo(r, r);
	return r;
}
function Classic(m) {
	this.m = m;
}
function cConvert(x) {
	if (x.s < 0 || x.compareTo(this.m) >= 0) return x.mod(this.m); else return x;
}
function cRevert(x) {
	return x;
}
function cReduce(x) {
	x.divRemTo(this.m, null, x);
}
function cMulTo(x, y, r) {
	x.multiplyTo(y, r);
	this.reduce(r);
}
function cSqrTo(x, r) {
	x.squareTo(r);
	this.reduce(r);
}
Classic.prototype.convert = cConvert;
Classic.prototype.revert = cRevert;
Classic.prototype.reduce = cReduce;
Classic.prototype.mulTo = cMulTo;
Classic.prototype.sqrTo = cSqrTo;
function bnpInvDigit() {
	if (this.t < 1) return 0;
	var x = this[0];
	if ((x & 1) == 0) return 0;
	var y = x & 3;
	y = y * (2 - (x & 15) * y) & 15;
	y = y * (2 - (x & 255) * y) & 255;
	y = y * (2 - ((x & 65535) * y & 65535)) & 65535;
	y = y * (2 - x * y % this.DV) % this.DV;
	return y > 0 ? this.DV - y : -y;
}
function Montgomery(m) {
	this.m = m;
	this.mp = m.invDigit();
	this.mpl = this.mp & 32767;
	this.mph = this.mp >> 15;
	this.um = (1 << m.DB - 15) - 1;
	this.mt2 = 2 * m.t;
}
function montConvert(x) {
	var r = nbi();
	x.abs().dlShiftTo(this.m.t, r);
	r.divRemTo(this.m, null, r);
	if (x.s < 0 && r.compareTo(BigInteger.ZERO) > 0) this.m.subTo(r, r);
	return r;
}
function montRevert(x) {
	var r = nbi();
	x.copyTo(r);
	this.reduce(r);
	return r;
}
function montReduce(x) {
	while (x.t <= this.mt2) x[x.t++] = 0;
	for (var i = 0; i < this.m.t; ++i) {
		var j = x[i] & 32767;
		var u0 = j * this.mpl + ((j * this.mph + (x[i] >> 15) * this.mpl & this.um) << 15) & x.DM;
		j = i + this.m.t;
		x[j] += this.m.am(0, u0, x, i, 0, this.m.t);
		while (x[j] >= x.DV) {
			x[j] -= x.DV;
			x[++j]++;
		}
	}
	x.clamp();
	x.drShiftTo(this.m.t, x);
	if (x.compareTo(this.m) >= 0) x.subTo(this.m, x);
}
function montSqrTo(x, r) {
	x.squareTo(r);
	this.reduce(r);
}
function montMulTo(x, y, r) {
	x.multiplyTo(y, r);
	this.reduce(r);
}
Montgomery.prototype.convert = montConvert;
Montgomery.prototype.revert = montRevert;
Montgomery.prototype.reduce = montReduce;
Montgomery.prototype.mulTo = montMulTo;
Montgomery.prototype.sqrTo = montSqrTo;
function bnpIsEven() {
	return (this.t > 0 ? this[0] & 1 : this.s) == 0;
}
function bnpExp(e, z) {
	if (e > 4294967295 || e < 1) return BigInteger.ONE;
	var r = nbi(), r2 = nbi(), g = z.convert(this), i = nbits(e) - 1;
	g.copyTo(r);
	while (--i >= 0) {
		z.sqrTo(r, r2);
		if ((e & 1 << i) > 0) z.mulTo(r2, g, r); else {
			var t = r;
			r = r2;
			r2 = t;
		}
	}
	return z.revert(r);
}
function bnModPowInt(e, m) {
	var z;
	if (e < 256 || m.isEven()) z = new Classic(m); else z = new Montgomery(m);
	return this.exp(e, z);
}

function bnNegate() {
	var r = nbi();
	BigInteger.ZERO.subTo(this, r);
	return r;
}

function bnAbs() {
	return this.s < 0 ? this.negate() : this;
}


BigInteger.prototype.copyTo = bnpCopyTo;
BigInteger.prototype.fromInt = bnpFromInt;
BigInteger.prototype.fromString = bnpFromString;
BigInteger.prototype.clamp = bnpClamp;
BigInteger.prototype.dlShiftTo = bnpDLShiftTo;
BigInteger.prototype.drShiftTo = bnpDRShiftTo;
BigInteger.prototype.lShiftTo = bnpLShiftTo;
BigInteger.prototype.rShiftTo = bnpRShiftTo;
BigInteger.prototype.subTo = bnpSubTo;
BigInteger.prototype.multiplyTo = bnpMultiplyTo;
BigInteger.prototype.squareTo = bnpSquareTo;
BigInteger.prototype.divRemTo = bnpDivRemTo;
BigInteger.prototype.invDigit = bnpInvDigit;
BigInteger.prototype.isEven = bnpIsEven;
BigInteger.prototype.exp = bnpExp;
BigInteger.prototype.toString = bnToString;
BigInteger.prototype.negate = bnNegate;
BigInteger.prototype.abs = bnAbs;
BigInteger.prototype.compareTo = bnCompareTo;
BigInteger.prototype.bitLength = bnBitLength;
BigInteger.prototype.mod = bnMod;
BigInteger.prototype.modPowInt = bnModPowInt;
BigInteger.ZERO = nbv(0);
BigInteger.ONE = nbv(1);
function bnClone() {
	var r = nbi();
	this.copyTo(r);
	return r;
}
function bnIntValue() {
	if (this.s < 0) {
		if (this.t == 1) return this[0] - this.DV; else if (this.t == 0) return -1;
	} else if (this.t == 1) return this[0]; else if (this.t == 0) return 0;
	return (this[1] & (1 << 32 - this.DB) - 1) << this.DB | this[0];
}
function bnByteValue() {
	return this.t == 0 ? this.s : this[0] << 24 >> 24;
}
function bnShortValue(){return this.t == 0 ? this.s : this[0] << 16 >> 16;}
function bnpChunkSize(r) {return Math.floor(Math.LN2 * this.DB / Math.log(r));}
function bnSigNum() {
	if (this.s < 0) return -1; else if (this.t <= 0 || this.t == 1 && this[0] <= 0) return 0; else return 1;
}
function bnpToRadix(b) {
	if (b == null) b = 10;
	if (this.signum() == 0 || b < 2 || b > 36) return "0";
	var cs = this.chunkSize(b);
	var a = Math.pow(b, cs);
	var d = nbv(a), y = nbi(), z = nbi(), r = "";
	this.divRemTo(d, y, z);
	while (y.signum() > 0) {
		r = (a + z.intValue()).toString(b).substr(1) + r;
		y.divRemTo(d, y, z);
	}
	return z.intValue().toString(b) + r;
}
function bnpFromRadix(s, b) {
	this.fromInt(0);
	if (b == null) b = 10;
	var cs = this.chunkSize(b);
	var d = Math.pow(b, cs), mi = false, j = 0, w = 0;
	for (var i = 0; i < s.length; ++i) {
		var x = intAt(s, i);
		if (x < 0) {
			if (s.charAt(i) == "-" && this.signum() == 0) mi = true;
			continue;
		}
		w = b * w + x;
		if (++j >= cs) {
			this.dMultiply(d);
			this.dAddOffset(w, 0);
			j = 0;
			w = 0;
		}
	}
	if (j > 0) {
		this.dMultiply(Math.pow(b, j));
		this.dAddOffset(w, 0);
	}
	if (mi) BigInteger.ZERO.subTo(this, this);
}
function bnpFromNumber(a, b) {
	if ("number" == typeof b) {
		if (a < 2) this.fromInt(1); else {
			this.fromNumber(a);
			if (!this.testBit(a - 1)) this.bitwiseTo(BigInteger.ONE.shiftLeft(a - 1), op_or, this);
			if (this.isEven()) this.dAddOffset(1, 0);
			while (!this.isProbablePrime(b)) {
				this.dAddOffset(2, 0);
				if (this.bitLength() > a) this.subTo(BigInteger.ONE.shiftLeft(a - 1), this);
			}
		}
	} else {
		
		for(var x=[],l=a>>3;l>=0;l--)x.push(Math.floor(256*Math.random()));
		
		var t = a&7;
		if (t > 0) x[0]&=(1<<t)-1;
			else x[0]=0;
			
		this.fromString(x, 256);
	}
}
function bnToByteArray() {
	var i = this.t, r = new Array();
	r[0] = this.s;
	var p = this.DB - i * this.DB % 8, d, k = 0;
	if (i-- > 0) {
		if (p < this.DB && (d = this[i] >> p) != (this.s & this.DM) >> p) r[k++] = d | this.s << this.DB - p;
		while (i >= 0) {
			if (p < 8) {
				d = (this[i] & (1 << p) - 1) << 8 - p;
				d |= this[--i] >> (p += this.DB - 8);
			} else {
				d = this[i] >> (p -= 8) & 255;
				if (p <= 0) {
					p += this.DB;
					--i;
				}
			}
			if ((d & 128) != 0) d |= -256;
			if (k == 0 && (this.s & 128) != (d & 128)) ++k;
			if (k > 0 || d != this.s) r[k++] = d;
		}
	}
	return r;
}
function bnEquals(a){return this.compareTo(a) == 0;}
function bnMin(a){return this.compareTo(a) < 0 ? this : a;}
function bnMax(a){return this.compareTo(a) > 0 ? this : a;}
function bnpBitwiseTo(a, op, r) {
	var i, f, m = Math.min(a.t, this.t);
	for (i = 0; i < m; ++i) r[i] = op(this[i], a[i]);
	if (a.t < this.t) {
		f = a.s & this.DM;
		for (i = m; i < this.t; ++i) r[i] = op(this[i], f);
		r.t = this.t;
	} else {
		f = this.s & this.DM;
		for (i = m; i < a.t; ++i) r[i] = op(f, a[i]);
		r.t = a.t;
	}
	r.s = op(this.s, a.s);
	r.clamp();
}
function op_and(x, y){return x & y;}
function bnAnd(a) {
	var r = nbi();
	this.bitwiseTo(a, op_and, r);
	return r;
}
function op_or(x, y){return x | y;}
function bnOr(a) {
	var r = nbi();
	this.bitwiseTo(a, op_or, r);
	return r;
}
function op_xor(x, y){return x ^ y;}
function bnXor(a) {
	var r = nbi();
	this.bitwiseTo(a, op_xor, r);
	return r;
}
function op_andnot(x, y){return x & ~y;}
function bnAndNot(a) {
	var r = nbi();
	this.bitwiseTo(a, op_andnot, r);
	return r;
}
function bnNot() {
	var r = nbi();
	for (var i = 0; i < this.t; ++i) r[i] = this.DM & ~this[i];
	r.t = this.t;
	r.s = ~this.s;
	return r;
}
function bnShiftLeft(n) {
	var r = nbi();
	if (n < 0) this.rShiftTo(-n, r); else this.lShiftTo(n, r);
	return r;
}
function bnShiftRight(n) {
	var r = nbi();
	if (n < 0) this.lShiftTo(-n, r); else this.rShiftTo(n, r);
	return r;
}
function lbit(x) {
	if (x == 0) return -1;
	var r = 0;
	if ((x & 65535) == 0) {
		x >>= 16;
		r += 16;
	}
	if ((x & 255) == 0) {
		x >>= 8;
		r += 8;
	}
	if ((x & 15) == 0) {
		x >>= 4;
		r += 4;
	}
	if ((x & 3) == 0) {
		x >>= 2;
		r += 2;
	}
	if ((x & 1) == 0) ++r;
	return r;
}
function bnGetLowestSetBit() {
	for (var i = 0; i < this.t; ++i) if (this[i] != 0) return i * this.DB + lbit(this[i]);
	if (this.s < 0) return this.t * this.DB;
	return -1;
}
function cbit(x) {
	var r = 0;
	while (x != 0) {
		x &= x - 1;
		++r;
	}
	return r;
}
function bnBitCount() {
	var r = 0, x = this.s & this.DM;
	for (var i = 0; i < this.t; ++i) r += cbit(this[i] ^ x);
	return r;
}
function bnTestBit(n) {
	var j = Math.floor(n / this.DB);
	if (j >= this.t) return this.s != 0;
	return (this[j] & 1 << n % this.DB) != 0;
}
function bnpChangeBit(n, op) {
	var r = BigInteger.ONE.shiftLeft(n);
	this.bitwiseTo(r, op, r);
	return r;
}
function bnSetBit(n){return this.changeBit(n, op_or);}
function bnClearBit(n){return this.changeBit(n, op_andnot);}
function bnFlipBit(n){return this.changeBit(n, op_xor);}
function bnpAddTo(a, r) {
	var i = 0, c = 0, m = Math.min(a.t, this.t);
	while (i < m) {
		c += this[i] + a[i];
		r[i++] = c & this.DM;
		c >>= this.DB;
	}
	if (a.t < this.t) {
		c += a.s;
		while (i < this.t) {
			c += this[i];
			r[i++] = c & this.DM;
			c >>= this.DB;
		}
		c += this.s;
	} else {
		c += this.s;
		while (i < a.t) {
			c += a[i];
			r[i++] = c & this.DM;
			c >>= this.DB;
		}
		c += a.s;
	}
	r.s = c < 0 ? -1 : 0;
	if (c > 0) r[i++] = c; else if (c < -1) r[i++] = this.DV + c;
	r.t = i;
	r.clamp();
}
function bnAdd(a) {
	var r = nbi();
	this.addTo(a, r);
	return r;
}
function bnSubtract(a) {
	var r = nbi();
	this.subTo(a, r);
	return r;
}
function bnMultiply(a) {
	var r = nbi();
	this.multiplyTo(a, r);
	return r;
}
function bnSquare() {
	var r = nbi();
	this.squareTo(r);
	return r;
}
function bnDivide(a) {
	var r = nbi();
	this.divRemTo(a, r, null);
	return r;
}
function bnRemainder(a) {
	var r = nbi();
	this.divRemTo(a, null, r);
	return r;
}
function bnDivideAndRemainder(a) {
	var q = nbi(), r = nbi();
	this.divRemTo(a, q, r);
	return new Array(q, r);
}
function bnpDMultiply(n) {
	this[this.t] = this.am(0, n - 1, this, 0, 0, this.t);
	++this.t;
	this.clamp();
}
function bnpDAddOffset(n, w) {
	if (n == 0) return;
	while (this.t <= w) this[this.t++] = 0;
	this[w] += n;
	while (this[w] >= this.DV) {
		this[w] -= this.DV;
		if (++w >= this.t) this[this.t++] = 0;
		++this[w];
	}
}
function NullExp() {}

	NullExp.prototype.convert = function(x){return x}
	NullExp.prototype.revert = function(x){return x}
	NullExp.prototype.mulTo = function(x,y,r){x.multiplyTo(y, r)}
	NullExp.prototype.sqrTo = function(x,r){x.squareTo(r)}

function bnPow(e){return this.exp(e, new NullExp())}

function bnpMultiplyLowerTo(a, n, r) {
	var i = Math.min(this.t + a.t, n);
	r.s = 0;
	r.t = i;
	while (i > 0) r[--i] = 0;
	var j;
	for (j = r.t - this.t; i < j; ++i) r[i + this.t] = this.am(0, a[i], r, i, 0, this.t);
	for (j = Math.min(a.t, n); i < j; ++i) this.am(0, a[i], r, i, 0, n - i);
	r.clamp();
}
function bnpMultiplyUpperTo(a, n, r) {
	--n;
	var i = r.t = this.t + a.t - n;
	r.s = 0;
	while (--i >= 0) r[i] = 0;
	for (i = Math.max(n - this.t, 0); i < a.t; ++i) r[this.t + i - n] = this.am(n - i, a[i], r, 0, 0, this.t + i - n);
	r.clamp();
	r.drShiftTo(1, r);
}
function Barrett(m) {
	this.r2 = nbi();
	this.q3 = nbi();
	BigInteger.ONE.dlShiftTo(2 * m.t, this.r2);
	this.mu = this.r2.divide(m);
	this.m = m;
}

Barrett.prototype.convert = function(x){
	if (x.s < 0 || x.t > 2 * this.m.t) return x.mod(this.m); else if (x.compareTo(this.m) < 0) return x; else {
		var r = nbi();
		x.copyTo(r);
		this.reduce(r);
		return r;
	}
}

Barrett.prototype.revert = function(x){return x}

Barrett.prototype.reduce = function(x){
	x.drShiftTo(this.m.t - 1, this.r2);
	if (x.t > this.m.t + 1) {
		x.t = this.m.t + 1;
		x.clamp();
	}
	this.mu.multiplyUpperTo(this.r2, this.m.t + 1, this.q3);
	this.m.multiplyLowerTo(this.q3, this.m.t + 1, this.r2);
	while (x.compareTo(this.r2) < 0) x.dAddOffset(1, this.m.t + 1);
	x.subTo(this.r2, x);
	while (x.compareTo(this.m) >= 0) x.subTo(this.m, x);
}

Barrett.prototype.mulTo = function(x, y, r) {
	x.multiplyTo(y, r);
	this.reduce(r);
}

Barrett.prototype.sqrTo = function barrettSqrTo(x, r) {
	x.squareTo(r);
	this.reduce(r);
}


function bnModPow(e, m) {
	var i = e.bitLength(), k, r = nbv(1), z;
	if (i <= 0) return r; else if (i < 18) k = 1; else if (i < 48) k = 3; else if (i < 144) k = 4; else if (i < 768) k = 5; else k = 6;
	if (i < 8) z = new Classic(m); else if (m.isEven()) z = new Barrett(m); else z = new Montgomery(m);
	var g = new Array(), n = 3, k1 = k - 1, km = (1 << k) - 1;
	g[1] = z.convert(this);
	if (k > 1) {
		var g2 = nbi();
		z.sqrTo(g[1], g2);
		while (n <= km) {
			g[n] = nbi();
			z.mulTo(g2, g[n - 2], g[n]);
			n += 2;
		}
	}
	var j = e.t - 1, w, is1 = true, r2 = nbi(), t;
	i = nbits(e[j]) - 1;
	while (j >= 0) {
		if (i >= k1) w = e[j] >> i - k1 & km; else {
			w = (e[j] & (1 << i + 1) - 1) << k1 - i;
			if (j > 0) w |= e[j - 1] >> this.DB + i - k1;
		}
		n = k;
		while ((w & 1) == 0) {
			w >>= 1;
			--n;
		}
		if ((i -= n) < 0) {
			i += this.DB;
			--j;
		}
		if (is1) {
			g[w].copyTo(r);
			is1 = false;
		} else {
			while (n > 1) {
				z.sqrTo(r, r2);
				z.sqrTo(r2, r);
				n -= 2;
			}
			if (n > 0) z.sqrTo(r, r2); else {
				t = r;
				r = r2;
				r2 = t;
			}
			z.mulTo(r2, g[w], r);
		}
		while (j >= 0 && (e[j] & 1 << i) == 0) {
			z.sqrTo(r, r2);
			t = r;
			r = r2;
			r2 = t;
			if (--i < 0) {
				i = this.DB - 1;
				--j;
			}
		}
	}
	return z.revert(r);
}

function bnGCD(a) {
	var x = this.s < 0 ? this.negate() : this.clone();
	var y = a.s < 0 ? a.negate() : a.clone();
	if (x.compareTo(y) < 0) {
		var t = x;
		x = y;
		y = t;
	}
	var i = x.getLowestSetBit(), g = y.getLowestSetBit();
	if (g < 0) return x;
	if (i < g) g = i;
	if (g > 0) {
		x.rShiftTo(g, x);
		y.rShiftTo(g, y);
	}
	while (x.signum() > 0) {
		if ((i = x.getLowestSetBit()) > 0) x.rShiftTo(i, x);
		if ((i = y.getLowestSetBit()) > 0) y.rShiftTo(i, y);
		if (x.compareTo(y) >= 0) {
			x.subTo(y, x);
			x.rShiftTo(1, x);
		} else {
			y.subTo(x, y);
			y.rShiftTo(1, y);
		}
	}
	if (g > 0) y.lShiftTo(g, y);
	return y;
}
function bnpModInt(n) {
	if (n <= 0) return 0;
	var d = this.DV % n, r = this.s < 0 ? n - 1 : 0;
	if (this.t > 0) if (d == 0) r = this[0] % n; else for (var i = this.t - 1; i >= 0; --i) r = (d * r + this[i]) % n;
	return r;
}
function bnModInverse(m) {
	var ac = m.isEven();
	if (this.isEven() && ac || m.signum() == 0) return BigInteger.ZERO;
	var u = m.clone(), v = this.clone();
	var a = nbv(1), b = nbv(0), c = nbv(0), d = nbv(1);
	while (u.signum() != 0) {
		while (u.isEven()) {
			u.rShiftTo(1, u);
			if (ac) {
				if (!a.isEven() || !b.isEven()) {
					a.addTo(this, a);
					b.subTo(m, b);
				}
				a.rShiftTo(1, a);
			} else if (!b.isEven()) b.subTo(m, b);
			b.rShiftTo(1, b);
		}
		while (v.isEven()) {
			v.rShiftTo(1, v);
			if (ac) {
				if (!c.isEven() || !d.isEven()) {
					c.addTo(this, c);
					d.subTo(m, d);
				}
				c.rShiftTo(1, c);
			} else if (!d.isEven()) d.subTo(m, d);
			d.rShiftTo(1, d);
		}
		if (u.compareTo(v) >= 0) {
			u.subTo(v, u);
			if (ac) a.subTo(c, a);
			b.subTo(d, b);
		} else {
			v.subTo(u, v);
			if (ac) c.subTo(a, c);
			d.subTo(b, d);
		}
	}
	if (v.compareTo(BigInteger.ONE) != 0) return BigInteger.ZERO;
	if (d.compareTo(m) >= 0) return d.subtract(m);
	if (d.signum() < 0) d.addTo(m, d); else return d;
	if (d.signum() < 0) return d.add(m); else return d;
}

var lowprimes = [ 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997 ];

var lplim = (1 << 26) / lowprimes[lowprimes.length - 1];

function bnIsProbablePrime(t) {
	var i, x = this.abs();
	if (x.t == 1 && x[0] <= lowprimes[lowprimes.length - 1]) {
		for (i = 0; i < lowprimes.length; ++i) if (x[0] == lowprimes[i]) return true;
		return false;
	}
	if (x.isEven()) return false;
	i = 1;
	while (i < lowprimes.length) {
		var m = lowprimes[i], j = i + 1;
		while (j < lowprimes.length && m < lplim) m *= lowprimes[j++];
		m = x.modInt(m);
		while (i < j) if (m % lowprimes[i++] == 0) return false;
	}
	return x.millerRabin(t);
}
function bnpMillerRabin(t) {
	var n1 = this.subtract(BigInteger.ONE);
	var k = n1.getLowestSetBit();
	if (k <= 0) return false;
	var r = n1.shiftRight(k);
	t = t + 1 >> 1;
	if (t > lowprimes.length) t = lowprimes.length;
	var a = nbi();
	for (var i = 0; i < t; ++i) {
		a.fromInt(lowprimes[Math.floor(Math.random() * lowprimes.length)]);
		var y = a.modPow(r, this);
		if (y.compareTo(BigInteger.ONE) != 0 && y.compareTo(n1) != 0) {
			var j = 1;
			while (j++ < k && y.compareTo(n1) != 0) {
				y = y.modPowInt(2, this);
				if (y.compareTo(BigInteger.ONE) == 0) return false;
			}
			if (y.compareTo(n1) != 0) return false;
		}
	}
	return true;
}
BigInteger.prototype.chunkSize = bnpChunkSize;
BigInteger.prototype.toRadix = bnpToRadix;
BigInteger.prototype.fromRadix = bnpFromRadix;
BigInteger.prototype.fromNumber = bnpFromNumber;
BigInteger.prototype.bitwiseTo = bnpBitwiseTo;
BigInteger.prototype.changeBit = bnpChangeBit;
BigInteger.prototype.addTo = bnpAddTo;
BigInteger.prototype.dMultiply = bnpDMultiply;
BigInteger.prototype.dAddOffset = bnpDAddOffset;
BigInteger.prototype.multiplyLowerTo = bnpMultiplyLowerTo;
BigInteger.prototype.multiplyUpperTo = bnpMultiplyUpperTo;
BigInteger.prototype.modInt = bnpModInt;
BigInteger.prototype.millerRabin = bnpMillerRabin;
BigInteger.prototype.clone = bnClone;
BigInteger.prototype.intValue = bnIntValue;
BigInteger.prototype.byteValue = bnByteValue;
BigInteger.prototype.shortValue = bnShortValue;
BigInteger.prototype.signum = bnSigNum;
BigInteger.prototype.toByteArray = bnToByteArray;
BigInteger.prototype.equals = bnEquals;
BigInteger.prototype.min = bnMin;
BigInteger.prototype.max = bnMax;
BigInteger.prototype.and = bnAnd;
BigInteger.prototype.or = bnOr;
BigInteger.prototype.xor = bnXor;
BigInteger.prototype.andNot = bnAndNot;
BigInteger.prototype.not = bnNot;
BigInteger.prototype.shiftLeft = bnShiftLeft;
BigInteger.prototype.shiftRight = bnShiftRight;
BigInteger.prototype.getLowestSetBit = bnGetLowestSetBit;
BigInteger.prototype.bitCount = bnBitCount;
BigInteger.prototype.testBit = bnTestBit;
BigInteger.prototype.setBit = bnSetBit;
BigInteger.prototype.clearBit = bnClearBit;
BigInteger.prototype.flipBit = bnFlipBit;
BigInteger.prototype.add = bnAdd;
BigInteger.prototype.subtract = bnSubtract;
BigInteger.prototype.multiply = bnMultiply;
BigInteger.prototype.divide = bnDivide;
BigInteger.prototype.remainder = bnRemainder;
BigInteger.prototype.divideAndRemainder = bnDivideAndRemainder;
BigInteger.prototype.modPow = bnModPow;
BigInteger.prototype.modInverse = bnModInverse;
BigInteger.prototype.pow = bnPow;
BigInteger.prototype.gcd = bnGCD;
BigInteger.prototype.isProbablePrime = bnIsProbablePrime;
BigInteger.prototype.square = bnSquare;

function pkcs1pad2(s, n) {
	var ba = new Array();
	var i = s.length - 1;
	while (i >= 0 && n > 0) {
		var c = s.charCodeAt(i--);
		if (c < 128) {
			ba[--n] = c;
		} else if (c > 127 && c < 2048) {
			ba[--n] = c & 63 | 128;
			ba[--n] = c >> 6 | 192;
		} else {
			ba[--n] = c & 63 | 128;
			ba[--n] = c >> 6 & 63 | 128;
			ba[--n] = c >> 12 | 224;
		}
	}
	ba[--n] = 0;
	
	while(n>2) ba[--n] = Math.ceil(255*Math.random());

	ba[--n] = 2;
	ba[--n] = 0;
	return new BigInteger(ba);
}

function b64tohex(s) {
	var ret = "";
	var i;
	var k = 0;
	var slop;
	for (i = 0; i < s.length; ++i) {
		if (s.charAt(i) == "=") break;
		v = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".indexOf(s.charAt(i));
		if (v < 0) continue;//= padding at end
		if (k == 0) {
			ret += int2char(v >> 2);
			slop = v & 3;
			k = 1;
		} else if (k == 1) {
			ret += int2char(slop << 2 | v >> 4);
			slop = v & 15;
			k = 2;
		} else if (k == 2) {
			ret += int2char(slop);
			ret += int2char(v >> 2);
			slop = v & 3;
			k = 3;
		} else {
			ret += int2char(slop << 2 | v >> 4);
			ret += int2char(v & 15);
			k = 0;
		}
	}
	if (k == 1) ret += int2char(slop << 2);
	return ret;
}

BigInteger.prototype.makeDMP1 = function (pm, sz) {
	var ys=BigInteger_YS(sz);
	var y=pm.L_1(sz), r=this.L_2(sz);
	
	var d = y[ys-1]*16777216+(y[ys-2]>>4);
		
	var i=0, c = 0;
	y[ys]++;
	while(i<=ys) y[i]=(c=(c>>28)-y[i++])&268435455;
	
	y.s = 0;
	y.t = ys+1;
	var i = r.t, j = i - ys, q;
	while (--j >= 0) {
		q = Math.floor(((r[--i]*4503599627370496)+(16777216*r[i-1])+268435456)/d);
		r[i] += y.am_ZERO(sz,q, r, j);
	}

	r.t = ys;
	r.r_(sz);
	return r;
}

function BigInteger_YS(s){
	switch(s){
		case 512: return 10;
		case 1024: return 19;
		default: return null;
	}
}

function BigInteger_NSH(s){
	switch(s){
		case 512: return 24;
		case 1024: return 20;
		default: return null;
	}
}

BigInteger.prototype.L_preset = function(i,k,u,l,t){
var r=nbi();
	for (var c=0; i >= 0; --i) {
		r[i+1] = this[i] >> k | c;
		c = (this[i] & u) << l;
	}
	r[0]=c;
	r.t=t;
	r.s=0;
	return r;
}

BigInteger.prototype.L_1 = function(size) {
	switch(size){
		case 512: return this.L_preset(9,4,15,24,11);
		case 1024: return this.L_preset(18,8,255,20,20);
		default: return this.lShift_SIZE();
	}
}

BigInteger.prototype.L_2 = function(size) {
	switch(size){
		case 512: return this.L_preset(18,4,15,24,20);
		case 1024: return this.L_preset(36,8,255,20,38);
		default: return 0;
	}
}

BigInteger.prototype.am_ZERO = function(sz, x,w,j) {
	switch(sz){
		case 512: return this.am_512(x,w,j);
		case 1024: return this.am_1024(x,w,j);
		default: return 0;
	}
}

BigInteger.prototype.am_512 = function(x, w, j) {
var i=0, c=0, n=10;
	var xl = x & 16383, xh = x >> 14;
	while (--n >= 0) {
		var l = this[i] & 16383;
		var h = this[i++] >> 14;
		var m = xh * l + h * xl;
		l = xl * l + ((m & 16383) << 14) + w[j] + c;
		c = (l >> 28) + (m >> 14) + xh * h;
		w[j++] = l & 268435455;
	}
	return c;
}

BigInteger.prototype.am_1024 = function(x, w, j) {
var i=0, c=0, n=19;
	var xl = x & 16383, xh = x >> 14;
	while (--n >= 0) {
		var l = this[i] & 16383;
		var h = this[i++] >> 14;
		var m = xh * l + h * xl;
		l = xl * l + ((m & 16383) << 14) + w[j] + c;
		c = (l >> 28) + (m >> 14) + xh * h;
		w[j++] = l & 268435455;
	}
	return c;
}

BigInteger.prototype.r_ = function(s){
	switch(s){
		case 512: this.r_512(); break;
		case 1024: this.r_1024(); break;
		default: return 0;
	}
}
BigInteger.prototype.r_512 = function(){
	this[0]>>=24;
	for (var i=1; i < 10; ++i) {
		this[i-1] |= (this[i] & 16777215) << 4;
		this[i]>>=24;
	}
}

BigInteger.prototype.r_1024 = function(){
	this[0]>>=20;
	for(var i=1; i<19; ++i){
		this[i-1] |= (this[i]&1048575)<<8;
		this[i]>>=20;
	}
}

function makeD(m){
	var u = m.clone(), v = new BigInteger("010001", 16);
	var a = nbv(1), b = nbv(0), c = nbv(0), d = nbv(1);
	while (u.signum() != 0) {
		while (!u.Evn()){
			u.Rshift2();
			if (!a.isEven() || !b.isEven()) {
				a.add2();
				b.sub2(m);
			}
			a.Rshift2();
			b.Rshift2();
		}
		while (!v.Evn()) {
			v.Rshift2();
			if (!c.isEven() || !d.isEven()) {
				c.add2();
				d.sub2(m);
			}
			c.Rshift2();
			d.Rshift2();
		}
		if (u.compareTo(v) >= 0) {
			u.subTo(v, u);
			a.subTo(c, a);
			b.subTo(d, b);
		} else {
			v.subTo(u, v);
			c.subTo(a, c);
			d.subTo(b, d);
		}
	}
	if (d.compareTo(m) >= 0) return d.subtract(m);
	if (d.signum() < 0) d.addTo(m, d); else return d;
	if (d.signum() < 0) return d.add(m); else return d;
}

BigInteger.prototype.Evn = function(){return this[0]&1}

BigInteger.prototype.Rshift2 = function() {
	this[0] = this[0] >> 1;
		for (var i=1; i<this.t; ++i){
			this[i - 1] |= (this[i] & 1) << 27;
			this[i] = this[i] >> 1;
		}
	this[this.t - 1] |= (this.s & 1) << 27;
}

BigInteger.prototype.add2 = function(){
	this[0]+=65537;
	this.t=1;
		if((c=this[0]>>28)>0){this.t=2,this[1]=c;}
	this[0]&=268435455;
}

BigInteger.prototype.sub2 = function(a){
	var i = 0, c = 0, m = Math.min(a.t, this.t);
	while (i < m) {
		c += this[i] - a[i];
		this[i++] = c & 268435455;
		c >>= 28;
	}
	c += this.s;
	while (i < a.t) {
		c -= a[i];
		this[i++] = c & 268435455;
		c >>= 28;
	}
	
	this.s = c < 0 ? -1 : 0;
	this.t = i;
}

BigInteger.prototype.sub1 = function(){
	var r = new BigInteger();
	
	var c = this[0] - 1;
	r[0] = c & 268435455;
	c >>= 28;
	var i = 1;
	while (i < this.t) {
		c += this[i];
		r[i++] = c & 268435455;
		c >>= 28;
	}

	r.s = 0;
	r.t = i;	
	return r;
}

BigInteger.prototype.multiply2 = function(a){
	var r = nbi();
	
	var i = this.t;
	r.t = i + a.t;
	while (--i >= 0) r[i] = 0;
	for (i = 0; i < a.t; ++i) r[i+this.t]=this.ammm(a[i],r,i,this.t);
	r.s = 0;

	
	return r;
}

BigInteger.prototype.ammm = function(x, w, j, n){
	var i=0,c=0;
	var xl = x & 16383, xh = x >> 14;
	while (--n >= 0) {
		var l = this[i] & 16383;
		var h = this[i++] >> 14;
		var m = xh * l + h * xl;
		l = xl * l + ((m & 16383) << 14) + w[j] + c;
		c = (l >> 28) + (m >> 14) + xh * h;
		w[j++] = l & 268435455;
	}
	return c;
}

BigInteger.prototype.fromMagic= function(sz){
	var r=function(){return Math.ceil(Math.random()*127)},f=r(),n;
	
	switch(sz){
		case 512: n=9;f>>=3; break;
		case 1024: n=18; break;
		default: return;
	}
	
	this.t=n+1;
	this.s=0;
	for(var i=0;i<n;i++)for(var m=0;m<4;m++)this[i]|=r()<<(m*7);
	this[n]=f;
}

BigInteger.prototype.sub1_SIZE = function(z){
	switch(z){
		case 512: return this.sub1_magic(10);
		case 1024: return this.sub1_magic(19);
		default: return;
	}
}

BigInteger.prototype.sub1_magic = function(m){
	var r = new BigInteger();

	for(var i=0,c=-1; i<m; i++){
		r[i]= (c+= this[i]) & 268435455;
		c >>= 28;
	}

	r.s = 0;
	r.t = i;
	return r;
}


BigInteger.prototype.sub1_d_SIZE = function(z,q){
	switch(z){
		case 512: return this.sub1_d_512(10,q);
		case 1024: return this.sub1_d_1024(19,q);
		default: return;
	}
}

BigInteger.prototype.sub1_d_512 = function(m,q){
	var r = new BigInteger();

	for(var i=0,c=-1; i<m; i++){
		r[i]= (c+= this[i]) & 268435455;
		c >>= 28;
	}

	
	var v = nbi();
	v.t = 20;
	for(var i=0; i<10; i++) v[i]=0;
	for (i=0; i<10; ++i) v[i+10]=r.amm_512(q[i],v,i);
	v.s = 0;

	
	return v;
}

BigInteger.prototype.amm_512 = function(x, w, j){
	var i=0,c=0;
	var xl = x & 16383, xh = x >> 14;
	
	var aa=(x>>14)*(this[9]&16383);
/*	var e = j+9;
	
	var q2 = (x&16383)*(this[9]&16363);
		q2+= (((x>>14)*(this[9]&16363))&16383)<<14;
		q2+= w[e];
*/	
	for(var n=9; n>=0; n--) {
		var l = this[i] & 16383;
		var h = this[i] >> 14;
		var m = xh * l + h * xl;
		var q = xl * l + ((m & 16383) << 14) + w[j] + c;
		c = (q >> 28) + (m >> 14) + xh * h;
		w[j] = q & 268435455;
		
		i++;
		j++;
	}
	
	var l2 = this[9]&16383;
	var m2 = (x>>14)*(this[9]&16383);
	
	
	
	return (q>>28) + (aa>>14);
}

BigInteger.prototype.big_dummy = function(x, w, j){
	var i=0,c=0;
	
	for(var n=9; n>=0; n--) {
		var m = (x >> 14) * (this[i] & 16383) + (this[i] >> 14) * (x & 16383);
		var q = (x & 16383) * (this[i] & 16383) + ((m & 16383) << 14) + w[j] + c;
		c = (q >> 28) + (m >> 14) + (x >> 14) * (this[i] >> 14);
		w[j++] = q & 268435455;
		i++;
	}
	return c;
}

BigInteger.prototype.sub1_d_1024 = function(m,q){
	var r = new BigInteger();

	for(var i=0,c=-1; i<m; i++){
		r[i]= (c+= this[i]) & 268435455;
		c >>= 28;
	}

	r.s = 0;
	r.t = i;

	var v = nbi();
	v.t = i + q.t;
	while (--i >= 0) v[i] = 0;
	for (i=0; i<q.t; ++i) v[i+r.t]=r.ammm(q[i],v,i,r.t);
	
	v.s = 0;

	
	return v;
}