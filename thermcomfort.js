/*
MIT License
* * Copyright (c)  2019 Alfonso Crisci, Marco Morabito and Alessandro Messeri 
* * @authors Alfonso Crisci, Marco Morabito and Alessandro Messeri 
* * Email: a.crisci@ibe.cnr.it

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

*/ 

// Define global constants 

var    Patm = 101325.0; // pascal
var    CpAir= 1004.0;
var    CpWat= 4186.0;
var    CpVap= 1805.0;
var    Hfg= 2501000.0;
var    RAir= 287.055;
var    TKelConv= 273.15;
var    PI   = Math.PI,
       pi = Math.PI,
       twopi = 2 * pi,
       rad  = PI / 180,
       radians = PI / 180,
       degrees = 180 / PI,
       J1970 = 2440588,
       J2000 = 2451545;

///////////////////////////////////////////////////////////////////////////////////////////
// format  

function OneDec(c) 
{
    return Math.round(10 * c) / 10;
}

function TwoDec(c) 
{
    return Math.round(100 * c) / 100;
}

function ThreeDec(c) 
{
    return Math.round(1000 * c) / 1000;
}

function FourDec(c) 
{
    return Math.round(10000 * c) / 10000;
}

function scientificNotation(c,e)
 {
    return c.toPrecision(e);
}

////////////////////////////////////////////////////////////////////////////////////////////
// math & trigonometric 

function radToDeg(angleRad) 
{
  return (180.0 * angleRad / Math.PI);
}

function degToRad(angleDeg) 
{
  return (Math.PI * angleDeg / 180.0);
}

function arrayMinIndex (array) {
  return array.indexOf(Math.min.apply(null, array));
}


function arrayMaxIndex (array) {
  return array.indexOf(Math.max.apply(null, array));
}


function linspace(x0, xN, dx){
  
    var n = Math.floor((xN - x0)/(dx));
    var x = [];
    for(var i =0; i < n; ++i){
        x.push(x0 + i*dx);
    }
   return x;
}

function getBaseLog(x, y) {
  return Math.log(y) / Math.log(x);
}

/** * @(#)pnorm.js and qnorm.js 
  * * Copyright (c) 2000 by Sundar Dorai-Raj
  * * @author Sundar Dorai-Raj
  * * Email: sdoraira@vt.edu
  * * This program is free software; you can redistribute it and/or
  * * modify it under the terms of the GNU General Public License 
  * * as published by the Free Software Foundation; either version 2 
  * * of the License, or (at your option) any later version, 
  * * provided that any use properly credits the author. 
  * * This program is distributed in the hope that it will be useful,
  * * but WITHOUT ANY WARRANTY; without even the implied warranty of
  * * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
  * * "Applied Statistics Algorithms" (1985) vol 22 no.3 Algorithm AS66 P. Griffiths and I. D.    * *  Hill, editor 
*/


function pnorm(z,tail) {
    
    if( tail === undefined ) { tail = false}
    
    z=parseFloat(z);
	
    var ltone= 7.0;
    var utzero= 18.66;
    con= 1.28;
    a1 = 0.398942280444;
    a2 = 0.399903438504;
    a3 = 5.75885480458;
    a4 = 29.8213557808;
    a5 = 2.62433121679;
    a6 = 48.6959930692;
    a7 = 5.92885724438;
    b1 = 0.398942280385;
    b2 = 3.8052e-8;
    b3 = 1.00000615302;
    b4 = 3.98064794e-4;
    b5 = 1.986153813664;
    b6 = 0.151679116635;
    b7 = 5.29330324926;
    b8 = 4.8385912808;
    b9 = 15.1508972451;
    b10= 0.742380924027;
    b11= 30.789933034;
    b12= 3.99019417011;

    
   if(z<0) {
      tail=!tail;
      z=-z;
    }
    if(z<=ltone || tail && z<=utzero) {
      y=0.5*z*z;
      if(z>con) {
        alnorm=b1*Math.exp(-y)/(z-b2+b3/(z+b4+b5/(z-b6+b7/(z+b8-b9/(z+b10+b11/(z+b12))))));
      }
      else {
        alnorm=0.5-z*(a1-a2*y/(y+a3-a4/(y+a5+a6/(y+a7))));
      }
    }
    else {
      alnorm=0;
    }
    if(!tail) alnorm=1-alnorm;
      return(alnorm);
  }

// ALGORITHM AS 111, APPL.STATIST., VOL.26, 118-121, 1977.
// Computes z=invNorm(p)

function qnorm(p) {
    
    p=parseFloat(p);
    split=0.42;
    a0=  2.50662823884;
    a1=-18.61500062529;
    a2= 41.39119773534;
    a3=-25.44106049637;
    b1= -8.47351093090;
    b2= 23.08336743743;
    b3=-21.06224101826;
    b4=  3.13082909833;
    c0= -2.78718931138;
    c1= -2.29796479134;
    c2=  4.85014127135;
    c3=  2.32121276858;
    d1=  3.54388924762;
    d2=  1.63706781897;
    q=p-0.5;
    
    if(Math.abs(q)<=split) {
      r=q*q;
      ppnd=q*(((a3*r+a2)*r+a1)*r+a0)/((((b4*r+b3)*r+b2)*r+b1)*r+1);
    }
    else {
      r=p;
      if(q>0) r=1-p;
      if(r>0) {
        r=Math.sqrt(-Math.log(r));
        ppnd=(((c3*r+c2)*r+c1)*r+c0)/((d2*r+d1)*r+1);
        if(q<0) ppnd=-ppnd;
      }
      else {
        ppnd=0;
      }
    } 
    return(ppnd);
  }


/**
 * Wind reduction at specific height 
 * @param {number} x, ref, fin
 * @return {number}
 * 
 */

function reducewind(x,ref,fin) {  
                                        if( ref === undefined ) { tresh = 10}
                                        if( fin === undefined ) { fin = 2}
                                        return(x*1/(Math.log(ref/0.01)/Math.log(fin/0.01)));
                               }

/**
 * Compute error erf function
 * @param {number} x
 * @return {number}
 * 
 */

function erf(x) {  x=parseFloat(x); 
                   return(2 * pnorm(x * Math.sqrt(2)) - 1);
		}


/////////////////////////////////////////////////////////////////////////////////////////////////
// Date related 

function ExcelDateToJSDate(serial) {
   var utc_days  = Math.floor(serial - 25569);
   var utc_value = utc_days * 86400;                                        
   var date_info = new Date(utc_value * 1000);

   var fractional_day = serial - Math.floor(serial) + 0.0000001;

   var total_seconds = Math.floor(86400 * fractional_day);

   var seconds = total_seconds % 60;

   total_seconds -= seconds;

   var hours = Math.floor(total_seconds / (60 * 60));
   var minutes = Math.floor(total_seconds / 60) % 60;

   return new Date(date_info.getFullYear(), date_info.getMonth(), date_info.getDate(), hours, minutes, seconds);
}

Date.prototype.getJulian = function() 
{
    return Math.floor((this / 86400000) - (this.getTimezoneOffset()/1440) + 2440587.5);
  
};


Date.prototype.isLeapYear = function() 
{
    var year = this.getFullYear();
    if((year & 3) !== 0) return false;
    return ((year % 100) !== 0 || (year % 400) === 0);
};


Date.prototype.getDOY = function() {
    var dayCount = [0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334];
    var mn = this.getMonth();
    var dn = this.getDate();
    var dayOfYear = dayCount[mn] + dn;
    if(mn > 1 && this.isLeapYear()) dayOfYear++;
    return dayOfYear;
};

String.prototype.toDate = function(format)
{
  var normalized      = this.replace(/[^a-zA-Z0-9]/g, '-');
  var normalizedFormat= format.toLowerCase().replace(/[^a-zA-Z0-9]/g, '-');
  var formatItems     = normalizedFormat.split('-');
  var dateItems       = normalized.split('-');

  var monthIndex  = formatItems.indexOf("mm");
  var dayIndex    = formatItems.indexOf("dd");
  var yearIndex   = formatItems.indexOf("yyyy");
  var hourIndex     = formatItems.indexOf("hh");
  var minutesIndex  = formatItems.indexOf("ii");
  var secondsIndex  = formatItems.indexOf("ss");

  var today = new Date();

  var year  = yearIndex>-1  ? dateItems[yearIndex]    : today.getFullYear();
  var month = monthIndex>-1 ? dateItems[monthIndex]-1 : today.getMonth()-1;
  var day   = dayIndex>-1   ? dateItems[dayIndex]     : today.getDate();

  var hour    = hourIndex>-1      ? dateItems[hourIndex]    : today.getHours();
  var minute  = minutesIndex>-1   ? dateItems[minutesIndex] : today.getMinutes();
  var second  = secondsIndex>-1   ? dateItems[secondsIndex] : today.getSeconds();

  return new Date(year,month,day,hour,minute,second);
};

function getDOY(datetime) 
{

  return(datetime.getDOY());
}

function toJulian(date) 
{ return date.valueOf() / (1000 *60*60 * 24) -0.5 + J1970; }  // è il calcolo JD corretto.

function fromJulian(j)  
{ return new Date((j + 0.5 - J1970) * (1000 *60*60 * 24)); } 

function toDays(date)  
 { return toJulian(date) - J2000; }

function parseISO8601String(dateString) 
    {
    var timebits = /^([0-9]{4})-([0-9]{2})-([0-9]{2})T([0-9]{2}):([0-9]{2})(?::([0-9]*)(\.[0-9]*)?)?(?:([+-])([0-9]{2})([0-9]{2}))?/;
    var m = timebits.exec(dateString);
    var resultDate;
    if (m) {
        var utcdate = Date.UTC(parseInt(m[1]),
                               parseInt(m[2])-1, // months are zero-offset (!)
                               parseInt(m[3]),
                               parseInt(m[4]), parseInt(m[5]), // hh:mm
                               (m[6] && parseInt(m[6]) || 0),  // optional seconds
                               (m[7] && parseFloat(m[7])*1000) || 0); // optional fraction
        // utcdate is milliseconds since the epoch
        if (m[9] && m[10]) {
            var offsetMinutes = parseInt(m[9]) * 60 + parseInt(m[10]);
            utcdate += (m[8] === '+' ? -1 : +1) * offsetMinutes * 60000;
        }
        resultDate = new Date(utcdate);
    } else {
        resultDate = null;
    }
    return resultDate;
}


/**
 * Given a year return if is a leap year.
 * @param {number} yr
 * @return {String}
 */


function isLeapYear(yr) 
{
  return ((yr % 4 === 0 && yr % 100 !== 0) || yr % 400 === 0);
}

/**
 * Given a date, return the name of the day for that date.
 * @param {Date} date
 * @return {string}
 */

function dayname_IT(date) 
  {
  var dayNumberNameMap = {
    0: 'Domenica',
    1: 'Lunedi',
    2: 'Martedi',
    3: 'Mercoledi',
    4: 'Giovedi',
    5: 'Venerdi',
    6: 'Sabato'},
      dayName,
      dayNumber;
 
  if(! date.getDay ) {
    throw TypeError('TypeError: Argument is not of type "Date"!');
  }
  
  dayNumber = date.getDay();
  dayName = dayNumberNameMap[dayNumber];
  return dayName;
}

/////////////////////////////////////////////////////////////////////////////////////////////////////
// sun related  


function sun_data(strtime,lat,lon,parameter) 
   { 
    var datetime=new Date(strtime); 
    var udtTimedHours=datetime.getHours() - 0;
    var udtTimedMinutes =datetime.getMinutes() - 0;
    var udtTimedSeconds = datetime.getSeconds() - 0;
    var udtLocationdLongitude = lon - 0;
    var udtLocationdLatitude = lat - 0;
    var dEarthMeanRadius = 6371.01;
    var dAstronomicalUnit = 149597890;
    var dDecimalHours = udtTimedHours + (udtTimedMinutes + udtTimedSeconds / 60) / 60;
    var dJulianDate = datetime.valueOf() / (1000.0 *60.0*60.0 * 24.0) - 0.5  + J1970;
    var dElapsedJulianDays = dJulianDate - 2451545;
    var dOmega = 2.1429 - 0.0010394594 * dElapsedJulianDays;
    var dMeanLongitude = 4.895063 + 0.017202791698 * dElapsedJulianDays;
    var dMeanAnomaly = 6.24006 + 0.0172019699 * dElapsedJulianDays;
    var dEclipticLongitude = dMeanLongitude + 0.03341607 * Math.sin(dMeanAnomaly) + 3.4894E-4 * Math.sin(2 * dMeanAnomaly) - 1.134E-4 - 2.03E-5 * Math.sin(dOmega);
    var dEclipticObliquity = 0.4090928 - 6.214E-9 * dElapsedJulianDays + 3.96E-5 * Math.cos(dOmega);
    var dSin_EclipticLongitude = Math.sin(dEclipticLongitude);
    var dY = Math.cos(dEclipticObliquity) * dSin_EclipticLongitude;
    var dX = Math.cos(dEclipticLongitude);
    var dRightAscension = Math.atan2(dY, dX);
    0 > dRightAscension && (dRightAscension += twopi);
    var dDeclination = Math.asin(Math.sin(dEclipticObliquity) * dSin_EclipticLongitude);
    var dGreenwichMeanSiderealTime = 6.6974243242 + 0.0657098283 * dElapsedJulianDays + dDecimalHours;
    var dLocalMeanSiderealTime = (15 * dGreenwichMeanSiderealTime +udtLocationdLongitude) * rad;
    var dHourAngle = dLocalMeanSiderealTime - dRightAscension;
    var dLatitudeInRadians = udtLocationdLatitude * rad;
    var dCos_Latitude = Math.cos(dLatitudeInRadians);
    var dSin_Latitude = Math.sin(dLatitudeInRadians);
    var dCos_HourAngle = Math.cos(dHourAngle);
    var udtSunCoordinatesdZenithAngle = Math.acos(dCos_Latitude * dCos_HourAngle * Math.cos(dDeclination) + Math.sin(dDeclination) * dSin_Latitude);
    dY = -Math.sin(dHourAngle);
    dX = Math.tan(dDeclination) * dCos_Latitude - dSin_Latitude * dCos_HourAngle;
    var udtSunCoordinatesdAzimuth = Math.atan2(dY,dX);
    0 > udtSunCoordinatesdAzimuth && (udtSunCoordinatesdAzimuth += twopi);
    udtSunCoordinatesdAzimuth /= rad;
    var dParallax = dEarthMeanRadius / dAstronomicalUnit * Math.sin(udtSunCoordinatesdZenithAngle);
    udtSunCoordinatesdZenithAngle = (udtSunCoordinatesdZenithAngle + dParallax) / rad;
    var azimuth = udtSunCoordinatesdAzimuth;
    var zenith = udtSunCoordinatesdZenithAngle;
    var elevation = 90 - udtSunCoordinatesdZenithAngle;
    if (elevation > 85.0) {var refractionCorrection = 0.0;} 
        else {
        var te = Math.tan (degToRad(elevation));
        if (elevation > 5.0) 
            {var refractionCorrection = 58.1 / te - 0.07 / (te*te*te) + 0.000086 / (te*te*te*te*te);} 
        else if (elevation > -0.575) 
               {var refractionCorrection = 1735.0 + elevation * (-518.2 + elevation * (103.4 + elevation * (-12.79 + elevation * 0.711) ) );}  
        else {var refractionCorrection = -20.774 / te;}
        refractionCorrection = refractionCorrection / 3600.0;
    }

    var solarZen = zenith - refractionCorrection;
    if ( parameter == "azimuth") {return(FourDec(azimuth))}
    else if ( parameter == "zenith") {return(FourDec(zenith))}
    else if ( parameter == "solarZenith") {return(FourDec(solarZen))}
    else if ( parameter == "elevation") {return(FourDec(elevation))}
    else if ( parameter == "declination") {return(dDeclination*(180/PI))}
    else if ( parameter == "JD") {return(dJulianDate)}
    else { return("Parameter not indicated!")};
     
}

/**
 * Given thoretical directed radiation of horizontal surface.
 * @param {number} jddate, az, elev, planezen, planeaz
 * @return {number}
 */

function radtheoric(jddate,elev,albedo,param)
{ 
  if( albedo === undefined ) { albedo = 0.3;};
  if( param === undefined ) { param  = "global";};
	
  var radcalcteoric;
  var SC = 1.361; //  kW/m2   ET solar radition I0 kW/m2 Solar constant
  var I0 = SC*(1+0.034*Math.cos((jddate)*2*pi/365)); //  atmospheric effect
  var A = 1.160 + 0.075 * Math.sin((jddate-274)*2*pi/365);
  var opt_depth = 0.174 + 0.035 * Math.sin((jddate-100)*2*pi/365);
  var air_mass = 1/Math.sin(elev*2*pi/360); 
  var IB = I0*Math.exp(-opt_depth*air_mass); //  Direct Beam 
  var IDH = IB*(0.095 + 0.04*Math.sin((jddate-100)*2*pi/365)); // Diffuse radiation 
  var ID = IDH*(1+Math.cos(pi-elev*2*pi/360))/2; // Diffuse radiation
  var IBH = IB*Math.sin(elev*2*pi/360);
  var IR =  albedo*(IBH+IDH)*(1+Math.cos(pi-elev*2*pi/360))/2; // reflected
  var ITot = IB+ID+IR; //  total
  
  if ( ITot <0) {ITot=0;IB=0;IR=0;};
  
  if (param == "global") {return(ITot)}
  else if (param == "direct") {return(IB)}
  else if (param == "diffuse") {return(ID)}
  else if (param == "reflected") {return(IR)}
  else  {return(-9999)}    

}

/**
 * Given thoretical directed radiation of tilted surface
 * @param {number} jddate, az, elev, planezen, planeaz
 * @return {number}
 */

function rad_direct_tilted(jddate,az,elev,planezen,planeaz) 
{
                            planezen=planezen/rad;
                            planeaz=planeaz/rad;
                            elev=elev/rad;
                            az=az/rad;
                            var rad_dir=radtheoric(jddate,elev,"direct");
                            var radinc=rad_dir *(Math.cos(elev)*Math.sin(planezen)*Math.cos(planeaz-az)+Math.sin(elev)*Math.cos(planezen));
                            return(rad_inc);
}

/**
 * Given sun elevation in degrees give value of projection factor.
 * @param {number} suneleve
 * @return {number}
 */

function proj(sunelev)
{
          if (sunelev < 0.0) {return 0.0};
          return 0.308 * Math.cos(rad * (sunelev* (0.998- (Math.pow(sunelev, 2.0) / 50000.0))));
}


/**
 * Given a temperature in celsius degree (degC), return the Fahrenheit degree value (degF).
 * @param {number} C
 * @return {number}
 */

function C2F(C) 
{
  if (typeof C !== 'number') {
                              throw TypeError('Celsius value must be a number');
                              }
  return (Math.round((C * 9) / 5 + 32,2));
}

/**
 * Given a temperature in Fahrenheit degree (degF), return  the celsius degree value (degF).
 * @param {number} F
 * @return {number}
 */

function F2C(F) 
{
  if (typeof F !== 'number') {
                             throw TypeError('Value must be a number');
                             }
 return(Math.round((5/9) * (F - 32),3));
}



/////////////////////////////////////////////////////////////////////////////////////////
//  wind  sector direction 

function compass_16(direction) 
 {
  var dir = ["N", "NNE", "NE", "ENE", "E", "ESE", "SE",
             "SSE", "S", "SSW", "SW", "WSW", "W", "WNW",
            "NW", "NNW"];
  var dirint=(((direction+11.25)/22.5));							   
  return(dir[parseInt(dirint % 16)]);
}



function compass_8(direction) 
{ var dir = ["N",  "NE", "E",  "SE",
             "S",  "SW", "W", "NW"];
  var dirint=(((direction+22.5)/45));							   
  return(dir[parseInt(dirint % 8)]);
}
  

////////////////////////////////////////////////////////////////////////////////////////////////////
// radiant temperature  

/** 
 * Given t air temperature in degC, rh relative humidity (%), shortwave  directed beam short-wavelength radiation (W/mq)the sun elevation,albedo gives and surface emissivity provides 
 * an assessment of Mean Radiant Temperature.
 * @param {number} t, rh, wind, rshort, sunelev
 * @return {number}
 */

function mrt_solar_proj(t,rh,solar,sunelev,albedo,emis_sfc,fdir)
{
  if( albedo === undefined ) { albedo = 0.3;};
  if( emis_sfc === undefined ) { emis_sfc = 0.97;};
  if( fdir === undefined ) { fdir = 0.8;};
  if( sunelev === undefined ) { sunelev = 90;};
  
  var temprad;
  var emiair;
  var tsk;
  var rshort=solar*fdir;
  var rdiffuse=solar-rshort;

  var sig = 5.67e-8;
  emiair = emis_atm(t,rh);
  tsk = t + 273.12;
  var ratio=0.0429*Math.sin(sunelev*rad)+0.345*Math.cos(sunelev*rad);
  var proj=0.308 * Math.cos(rad * (sunelev* (0.998- (Math.pow(sunelev, 2.0) / 50000.0))));
  
  temprad= Math.pow((emiair * Math.pow(tsk, 4) + (1-albedo) * (rdiffuse) / (sig* emis_sfc)+(1-albedo) * proj * ratio* ((rshort-rdiffuse)/(sig*emis_sfc))),0.25)- 273.16;
  
  return temprad;
}

/**
 * Given mean radiant temperature t air temperature (degC), g Globe Temeperature in degC, wind speed in m/s 
 * and diameter in mm.
 * @param {number} t Air temperature , tg Globe Temeperature, wind speed and diameter. 
 * @return {number}
 */

function mrt_thorsson(t, tg, wind, diam)
{        if ( diam === undefined) {diam=0.15;} ;
         var emis_globe = 0.97;
         var stefanb = 0.0000000567;
         return Math.pow(Math.pow(tg + 273.15, 4) + ((1.335 * Math.pow(10,8) * Math.pow(wind,0.71)) /(emis_globe*Math.pow(diam,0.4))) * (tg - t), 0.25) - 273.15;
}






function fglob_sphere(Tglobe_prev,Tair,rh,speed,solar,zenith,pair,alb_sfc,fdir,diam)
                        {
                        if(zenith === undefined )   {zenith = 0.0000000001;};
                        if(zenith <= 0 )            { zenith = 0.0000000001;};
                        if(zenith > 1.57 )          { zenith = 1.57;};
                        if(pair === undefined )     { pair =1013.25;};
                        if(alb_sfc === undefined )  { alb_sfc = 0.4;};
                        if(fdir === undefined )     { fdir = 0.8;}; 
                        if(diam === undefined )     { diam = 0.05;}; 
                       
                        var cza,dT,Tref,h,Tglobe;
                        var speedmin = 0.13;  
                        var alb_globe = 0.05;
                        var emis_globe = 0.95;
                        var emis_sfc = 0.999;
                        var stefanb = 0.000000056696;
                        var Tsfc = Tair;
                        var RH=rh*0.01;  
                        var emis_air;
                        converge = 0.05;
                        
                        cza = Math.cos(zenith);
                         
                        Tref = 0.5 * (Tglobe_prev + Tair);
                          
                        h = h_sphere_in_air(Tref, speed, pair);
                          
                        Tglobe= Math.pow(0.5 * (emis_atm(Tair,RH) * Math.pow( Tair,4) + emis_sfc * Math.pow(Tsfc,4)) 
                                      - h / (emis_globe * stefanb) * (Tglobe_prev - Tair) 
                                      + solar / (2 * emis_globe * stefanb) * (1 - alb_globe) * (fdir * (1 / (2 * cza) - 1) + 1 + alb_sfc),0.25); 

                         dT = Math.abs(Tglobe - Tglobe_prev);
                     
                         return(dT);
                        }

/**
 *  Given t air temperature (degC), rh relative humidity (%) , speed as wind speed in m/s, 
 *  solar as global radiation in  Watt/mq, solar zenith in radians, pair Air Pressure in millibar (hPa),
 *  alb_sfc as the mean albedo of surrounding surfaces, fdir is the ratio between diffuse and directed radiation, 
 *  irad is 1 if the radiation is taken into account , diam is the diameter of heat globe in meters,
 *  maxair and minair are  the range respect to air temperature where  solution was searched and prec is the precision.
 *  @param {number} t,rh,wind,solar,zenith,pair,alb_sfc,fdir,irad,diam,maxair,minair,prec
 *  @return {number} 
 */

function tglob_sphere(t,rh,speed,solar,zenith,pair,alb_sfc,fdir,diam,maxair,minair,prec){
  
                         if( pair === undefined )     { pair =1013.25;};
                         if( alb_sfc === undefined )  { alb_sfc = 0.4;};
                         if( fdir === undefined )     { fdir = 0.8;}; 
                         if( diam === undefined )     { diam = 0.05;}; 
                         if( minair === undefined )     { minair = 2;}; 
                         if( maxair === undefined )     { maxair = 10;}; 
                         if( prec === undefined )     { prec = 0.01;}; 
  
                         if(solar > 15 &&  zenith > 1.54) {zenith = 1.54;}; 
	                       if(solar > 900 &&  zenith > 1.52) {zenith = 1.52;}; 
                   
  
                         var Tair = t + 273.15;
                         var map1=[];
                         var array1 = linspace(Tair-minair,Tair+maxair,prec);
                         for (var i = 0; i < array1.length; i++) {map1[i]=fglob_sphere(array1[i],Tair,rh,speed,solar,zenith,pair,alb_sfc,fdir,diam)}
                         return(array1[arrayMinIndex(map1)]-273.15);
                         }




/**
 * Given a air temperature t (Celsius degree), globe temperature (degC), wind speed in m/s and diam of globe in meters compute the mean radiant temperature (Celsius degrees) ;
 * @param {number} t, tg, wind, diam_glob
 * @return {number}
 */

function mrt_globe(t, tg, wind, diam_globe,emis_globe)

{        if ( diam_globe === undefined) {diam_globe = 0.05;} ; 
 
         if ( emis_globe === undefined) {emis_globe = 0.97;} ; 
 
         var stefanb = 0.0000000567;
 
         return Math.pow((Math.pow(tg + 273.15, 4) + ((1.1 * Math.pow(10,8) * Math.pow(wind,0.6)) /(emis_globe*Math.pow(diam_globe,0.4))) * (tg - t)), 0.25)- 273.15;
}


////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Psycrometrics related functions.


/**
 * Given air temperature (Celsius), relative humidity (%)  gives natural wetbulb in celsius degrees.
 * Formulation from Stull 2011, Journal of Applied Meteorology and Climatology.
 * @param {number} t,rh
 * @return {number}
 */

function wetbulb_stull(t,rh) 
{
     c = new Array(6);
     c[0] =0.151977;
     c[1] =8.313659;
     c[2] =1.676331;
     c[3] =0.00391838;
     c[4] =0.023101;
     c[5] =4.686035;
  
    var wetbulb = t * Math.atan(c[0] * Math.sqrt(rh + c[1])) 
                     + Math.atan(t + rh) - Math.atan(rh - c[2]) 
                     + c[3] * (Math.pow(rh,3/2)) * Math.atan(c[4] * rh) - c[5];
    return(wetbulb)
}





function fnatural_wetbulb(Twb_prev,Tair,rh,wspeed,solar,zenith,pair,alb_sfc,fdir,irad)
                        {
                       
                         if( alb_sfc === undefined ) {alb_sfc = 0.4;};
                         if( fdir === undefined ) { fdir = 0.8;}; 
                         if( irad === undefined ) {irad = 1;};
                              
                         var dT,Tref,h,Twb,Fatm,density,eair;
                         var speedmin = 0.13;  
                         var emis_sfc = 0.999;
                         var stefanb= 0.000000056696;
                           
                        /* heat capaticy of dry air at constant pressure */
                        
                         var cp=1003.5;
                         var m_air=28.97;
                         var m_h2o=18.015;
                         var r_gas=8314.34;
                         var r_air=r_gas / m_air;
                         var ratio=cp * m_air/ m_h2o;
                         var Pr=cp / (cp + (1.25 * r_air));
  
                        // Wick constants
                        
                        var emis_wick = 0.95;   // emissivity
                        var alb_wick = 0.4;    // albedo
                        var diam_wick = 0.007; // diameter (in m)
                        var len_wick = 0.0254; // length (in m)
  
                        // Globe constants
                        
                    
                        var Tsfc = Tair;
                        var RH=rh * 0.01;  
                        var emis_air= emis_atm(Tair,RH);
                            eair = RH * esat(Tair);   
                            Tref = 0.5 * (Twb_prev + Tair);
                          
                            // Radiative heating term	
                          
                            Fatm = stefanb * emis_wick * (0.5 * (emis_air * Math.pow(Tair, 4) 
                                   + emis_sfc * Math.pow(Tsfc, 4))  - Math.pow(Twb_prev, 4)) 
                                   + (1 - alb_wick) * solar * ((1 - fdir) * (1 + 0.25 * diam_wick / len_wick) 
                                   + ((Math.tan(zenith) / 3.1416) + 0.25 * diam_wick / len_wick) * fdir + alb_sfc);
    
                           // Schmidt number
                           
                           density = (pair * 100) / (Tair * r_air);
                       
                           var Sc = viscosity(Tair) / (density * diffusivity(Tref, pair));
                           
                           // Calculate the convective heat transfer coefficient for a long cylinder in cross flow
                          
                            h = h_cylinder_in_air(Twb_prev, wspeed, pair,speedmin, diam_wick);    
                          
                           // Calculate the saturation vapor pressure (hPa) over liquid water
                          
                            var ewick = esat(Twb_prev);
                           
                         
                           // Calculate the heat of evaporation, J/(kg K)
                            
                           var evap = h_evap(Twb_prev); 
                              
                          
                           Twb = Tair - (evap/ratio) * ((ewick - eair) / (pair - ewick)) * Math.pow((Pr / Sc),0.56) + Fatm / h * irad;
                           
                           dT = Twb - Twb_prev;
                               
                           return(Math.abs(dT));
                         }
   
   /**
 *  Given t air temperature (degC), rh relative humidity (%) , wspeed as wind speed in m/s, 
 *  solar as global radiation in  Watt/mq, solar zenith in radians, pair Air Pressure in millibar (hPa),
 *  alb_sfc as the mean albedo of surrounding surfaces, fdir is the ratio between diffuse and directed radiation, 
 *  irad is 1 if the radiation is taken into account , diam is the diameter of heat globe in meters,
 *  maxair and minair are  the range respect to air temperature where  solution was searched and prec is the precision 
 *  gives natural wetbulb temperature. 
 *  @param {number} t,rh,wind,solar,zenith,pair,alb_sfc,fdir,irad,diam,maxair,minair,prec
 *  @return {number} 
 */
 
function natural_wetbulb(t,rh,wspeed,solar,zenith,pair,alb_sfc,fdir,irad,maxair,minair,prec){
                        
                         if( zenith === undefined )    { zenith = 0.0000000001;};
                         if( zenith <= 0 )             { zenith = 0.0000000001;};
                         if( zenith > 1.57 )           { zenith = 1.57;};
                        
                         if ( wspeed === undefined )  { wspeed = 0.13};
                         if ( solar === undefined )   { solar = 0};
                         if ( minair === undefined )  { minair = 2;}; 
                         if ( maxair === undefined )  { maxair = 10;}; 
                         if ( pair === undefined )    { pair = 1010;};
                         if ( alb_sfc === undefined)  { alb_sfc = 0.4;};
                         if ( fdir === undefined )    { fdir = 0.8;}; 
                         if ( irad === undefined )    { irad = 1;};
                         if ( prec === undefined )    { prec = 0.1;};
                       
                         var Tair = t + 273.15;
                         var Twb_prev = dewpoint(t,rh) + 273.15;
                         var map1=[];
                         var array1 = linspace(Twb_prev-minair,Tair+maxair,prec);
                         for (var i = 0; i < array1.length; i++) {map1[i]=fnatural_wetbulb(array1[i],Tair,rh,wspeed,solar,zenith,pair)};
                         return(array1[arrayMinIndex(map1)]-273.15);
                         }




/**
 * Purpose: to calculate the convective h the heat tranfer coefficient for flow around a sphere. tk (Kelvin), 
 * speed as wind speed in m/s, pair air pressure in millibar(hPa) , the minimal wind speed and diameter of the globe.
 * Reference; BSL, page 23.;
 * @param {number} t, speed,pair,speedmin,diam_globe;
 * @return {number}
 */
                             
function h_sphere_in_air(tk,speed,pair,speedmin,diam_globe)
    {
       if( diam_globe === undefined ) {diam_globe=0.05;};
       if( speedmin === undefined ) {speedmin=0.13;};
       if( pair === undefined ) {pair=1013.25;};
       var Rair = 8314.34 / 28.97;
       var Pr = 1003.5 / (1003.5 + 1.25 * Rair);
       var thermal_con = (1003.5 + 1.25 * 8314.34 / 28.97) * viscosity(tk);
       var density = (pair * 100) / (Rair * tk);  // kg/m3;
       if  (speed < speedmin ) {speed = speedmin};
       var Re = (speed * density * diam_globe)/ viscosity(tk);
       var Nu = 2 + 0.6 * Math.pow(Re,0.5) * Math.pow(Pr, 0.3333);
       return (Nu * thermal_con)/ diam_globe; // W/(m2 K);
   }


 /**
 * Purpose: to calculate the convective heat tranfer coefficient for heat flow around a cylinder tk in degK
 * and air pressure in millibar(hPa).
 * Reference : Bird, Stewart, && Lightfoot (BSL), page 409.;
 * @param {number} t, speed,pair,speedmin,diam_globe
 * @return {number}
 */ 
    
function h_cylinder_in_air(tk,speed,pair,speedmin,diam_wick){
   
   if( diam_wick === undefined ) { diam_wick=0.007;};
   if( speedmin === undefined )  { speedmin=0.13;};
   if( pair === undefined )      { pair=1010;};
           
   var m_air = 28.97;
   var r_gas = 8314.34;
   var r_air = r_gas / m_air;
   var cp = 1003.5; // heat capaticy at constant pressure of dry air
   var Pr = cp / (cp + (1.25 * r_air));
  
  // Calculate the thermal conductivity of air, W/(m K)
  
  var thermal_con = (cp + 1.25 * r_gas / m_air) * viscosity(tk);
                                   
  // Density of the air
  
  var density = (pair * 100) / (r_air * tk);
  
  if (speed < speedmin) {speed = speedmin};
  
  // Reynolds number
  
  var Re = speed * density * diam_wick / viscosity(tk);
  
  //  Nusselt number
  
  var Nu = 0.281 * Math.pow(Re,0.6) * Math.pow(Pr, 0.44);
  
  // Convective heat transfer coefficient in W/(m2 K) for a long cylinder in cross flow
  var h_cylinder_in_air = Nu * thermal_con / diam_wick ; 
  
  return(h_cylinder_in_air);
}

                             
/**
 * Given a air temperature tk (degK) calculate the heat of evaporation.
 * Purpose: to calculate the convective heat tranfer coefficient for flow around a sphere.; t in K
 * Reference : Bird, Stewart, && Lightfoot (BSL), page 409.;

 * @param {number} tk
 * @return {number}
 */

function h_evap(tk){
   var evap = ((313.15 - tk) / 30 )* (-71100) + 2407300;
  return(evap);
}


/**
 * Given a air emissivity by using temperature in degK and relative umidity ( number)
 * Purpose: to calculate the convective heat tranfer coefficient for flow around a sphere.; t in K
 * Reference; Oke (2nd edition), page 373.;
 * @param {number} tk,rh
 * @return {number}
 */

function emis_atm(tk,rh)
{

                  var e = rh * esat(tk);
                  return(0.575 * Math.pow(e,0.143));
}                             
 
 /**
 * Calculate the saturation vapor pressure (mb) over liquid water given the temperature (degK).;
 * Reference Buck's (1981) approximation (eqn 3) of Wexler's (1976) formulae.;
 * @param {number} tk
 * @return {number}

 */  

function esat (tk) 
{
                  var esat= 1.004 *(6.1121 * Math.exp(17.502 * (tk - 273.15) / (tk - 32.18)));
                  return(esat);  
}

/**
 * Given a air temperature tk (degK) compute the viscosity of air in kg/(m s).
 * Reference; BSL, page 23.;
 * @param {number} tk
 * @return {number}
 */

              
function viscosity(tk)
{

                       var omega = (tk / 97 - 2.9) / 0.4 * (-0.034) + 1.048;
                       return 0.0000026693 * Math.pow(28.97 * tk,0.5) / (3.617 * 3.617 * omega );
}



/**
 * Given a air temperature tk (degK) and air pressure in millibar (hPa) compute the heat diffusivity in air.
 * Reference; BSL, page 23.;
 * @param {number} tk, pairt
 * @return {number}
 */

function diffusivity(tk, pair) {
  
   if( pair === undefined ) {pair=1013.25;};
  
  var pcrit13 = Math.pow(36.4 * 218, 1 / 3);
  var tcrit512 = Math.pow(132 * 647.3,(5 / 12));
  var Tcrit12 = Math.pow((132 * 647.3), 0.5);
  var Mmix = Math.pow((1 / 28.97 + 1 / 18.015),0.5);
  var diffusivity = 0.000364 * Math.pow((tk / Tcrit12),2.334) * pcrit13 * tcrit512 * Mmix / (pair / 1013.25) * 0.0001;
 return(diffusivity);
}


/**
 * Given a air temperature t (degC) and td dewpoint  (degC) compute the relative humidity
 * Reference; BSL, page 23.;
 * @param {number} t, td
 * @return {number}
 */

function fRH(t,td)
			{
				var rh;
				rh = 100*(es(td)/ es(t));
				return rh;
			}




/*
 * Given air temperature T (Celsius)  function gives Saturation Vapor Pressure for Ice . Dimension of outcomes in Pascal (hPa)
 * Saturation Vapor Pressure formula for range -100..0 Deg. C.
 * Hardy B, 1998,"ITS-90 Formulations for Vapor Pressure, Frostpoint Temperature,Dewpoint Temperature, and Enhancement Factors in the Range 100 to +100 C".
 * Proceedings of the Third International Symposium on Humidity & Moisture",Teddington, London, England, April 1998
*/

function pvsIce(T) 
{
			       var k0 = -5.8666426e3;
			       var k1 = 2.232870244e1;
			       var k2 = 1.39387003e-2;
			       var k3 = -3.4262402e-5;
			       var k4 = 2.7040955e-8;
			       var k5 = 6.7063522e-1;
                   var lnP = k0/T + k1 + (k2 + (k3 + (k4*T))*T)*T + k5*Math.log(T);
                   return Math.exp(lnP);
}


/**
 * Given air temperature T (deC)  function gives Saturation Vapor Pressure. Dimension of outcomes in kiloPascal (kPa)
 * Saturation Vapor Pressure formula for range 273..678 Deg. K. 
 * Equation (30) in Section 8.1 "The Saturation-Pressure Equation (Basic Equation),Erlangen, Germany, September 1997.
 * @param {number} T
 * @return {number}
 */

function pvsWater(T) 
{
  
                   var n1 = 0.11670521452767e4;
                   var n6 = 0.14915108613530e2;
                   var n2 = -0.72421316703206e6;
                   var n7 = -0.48232657361591e4;
                   var n3 = -0.17073846940092e2;
                   var n8 = 0.40511340542057e6;
                   var n4 = 0.12020824702470e5;
                   var n9 = -0.23855557567849;
                   var n5 = -0.32325550322333e7;
                   var n10 = 0.65017534844798e3;

                   var th = T+n9/(T-n10);
                   var A = (th+n1)*th+n2;
                   var B = (n3*th+n4)*th+n5;
                   var C = (n6*th+n7)*th+n8;

                   var p = 2*C/(-B+Math.sqrt(B*B-4*A*C));
                   p *= p;
                   p *= p;
                   return p*1e6;
}

/**
 * Given air temperature T (Celsius)  function gives Saturation Vapor Pressure. Dimension of outcomes in Pascal (hPa)
 *
 * @param {number} t
 * @return {number}
 */

function PVS(t)
{
  t=t+273.16;
  var minT = 173; // -100 Deg. C.
  var maxT = 678;
  var noresp = -9999;
  var pvsresp;
  
  if (t < minT || t> maxT) 
     {return noresp;}
  
  else if (t<273.15)
       {pvsresp=pvsIce(t)/100;}
  else
       {pvsresp=pvsWater(t)/100;}
  
  return(TwoDec(pvsresp));
}



/**
 * Given air temperature (Celsius), relative humidity (%) and pressure ( pa) give deficit of saturation in delta hPA
 *
 * @param {number} t,rh
 * @return {number}
 */

function deficitsat(t,rh) 
{
  var pws = PVS(t);
  var pae = rh/100*pws;
  return (pws-pae);
}


/**
 * Given air temperature (Celsius) gives  saturation  pressure in hPa.
 * @param {number} t,rh
 * @return {number
 */

function es(t)
{
  var es_air, tk,i;
  g = new Array(8);
  g[0] =-2.8365744E3;
  g[1] =-6.028076559E3;
  g[2] =1.954263612E1;
  g[3] =-2.737830188E-2;
  g[4] =1.6261698E-5;
  g[5] =7.0229056E-10;
  g[6] =-1.8680009E-13;
  g[7] =2.7150305;
  

  tk = t+273.15; 
  
  es_air = g[7]*Math.log(tk);
  
  for ( var i = 0; i < 7; i ++ )
         {es_air = es_air+g[i]*Math.pow(tk,i-2)};
  
  var es = Math.exp(es_air)*0.01;
  
  return es;
}



/**
 * Given air temperature (Celsius), relative humidity (%).
 * @param {number} t,rh
 * @return {number}
 */

function pvap(t,rh)
			{
				var E;
				E = es(t) * (rh/100);
				return E;
			}


/**
 *  Given a air temperature t (degC) and air relative humidity  (rh)  and formula give the dew-point in degC.
 *  @param {number} t,rh,formula
 *  @return {number}
 */

function dewpoint(t,rh,formula) {
         if (formula == undefined) {formula == "NOAA"}
         var RHD = rh / 100;
         if (formula == "Paroscientific") 
             {return 237.3 * (Math.log(RHD) / 17.27 + t / (237.3 + t)) / (1 - Math.log(RHD) / 17.27 - t / (237.3 + t));}
         else if  (formula == "Sonntag") 
             {return 243.12 * (Math.log(RHD) / 17.62 + t / (243.12 + t)) / (1 - Math.log(RHD) / 17.62 - t / (243.12 + t));}
         else 
             {return 243.5 * (Math.log(RHD) / 17.67 + t / (243.5 + t)) / (1 - Math.log(RHD) / 17.67 - t / (243.5 + t));}
   

}


//////////////////////////////////////////////////////////////////////////////////////////////////
// Thermal Confort index section

/**
 * Given PMV value and Metabolic energy production M (58 to 400 W/m2) return the PPD Index ISO 7730. 
 * @param {number} PMV
 * @return {number}
 */

function PPD(PMV) 
            {
                   var PPD=100-95*Math.exp(-0.03353*Math.pow(PMV,4)-0.2179*Math.pow(PMV,2))
                   return(Math.round((PPD)*10)/10);
            }
  




  
/**
 * Given a temperature t (Celsius), relative humidity rh (%), wind ( m/sec), mean radiant temperature trad (degC),
 * M metabolism (met) , W external work ( generally 0) and clothing insulation (clo) 
 * gives perceived PMV (Predicted Mean Vote) for moderate thermal environements following ISO 7730.
 * @param {number} t,rh,wind,trad,M,W,clo
 * @return {number} 
 * @customfunction
 */

function PMV_ISO7730(t,rh,wind,trad,M,W,clo) 
    {
     
    var pa, icl, mw, fcl, hcf, taa, tra, tcla, p1, p2, p3, p4,
    p5, xn, xf, eps, hcn, hc, tcl, hl1, hl2, hl3, hl4, hl5, hl6,
    ts, pmv, ppd, n;

    pa = rh * 10 * Math.exp(16.6536 - 4030.183 / (t + 235));

    icl = 0.155 * clo; //thermal insulation of the clothing in M2K/W
    mw = M - W; //internal heat production in the human body
    
    if (icl <= 0.078) {fcl = 1 + (1.29 * icl)}
    
    else {fcl = 1.05 + (0.645 * icl)};

    //heat transf. coeff. by forced convection
  
    hcf = 12.1 * Math.sqrt(wind);
    taa = t + 273;
    tra = trad + 273;
    tcla = taa + (35.5 - t) / (3.5 * icl + 0.1);

    p1 = icl * fcl;
    p2 = p1 * 3.96;
    p3 = p1 * 100;
    p4 = p1 * taa;
    p5 = 308.7 - 0.028 * mw + p2 * Math.pow(tra / 100, 4);
    xn = tcla / 100;
    xf = tcla / 50;
    eps = 0.00015;

    n = 0;
  
    while (Math.abs(xn - xf) > eps) {
        xf = (xf + xn) / 2;
        hcn = 2.38 * Math.pow(Math.abs(100.0 * xf - taa), 0.25);
        if (hcf > hcn) hc = hcf;
        else hc = hcn;
        xn = (p5 + p4 * hc - p2 * Math.pow(xf, 4)) / (100 + p3 * hc);
        ++n;
        if (n > 150) {
              return('Max iterations exceeded');
        }
    }

    tcl = 100 * xn - 273;

    // heat loss diff. through skin 
    hl1 = 3.05 * 0.001 * (5733 - (6.99 * mw) - pa);
    // heat loss by sweating
    
    if (mw > 58.15) {hl2 = 0.42 * (mw - 58.15)}
    
    else 
    {hl2 = 0};
    
    // latent respiration heat loss 
    hl3 = 1.7 * 0.00001 * M * (5867 - pa);
    // dry respiration heat loss
    hl4 = 0.0014 * M * (34 - t);
    // heat loss by radiation  R
    hl5 = 3.96 * fcl * (Math.pow(xn, 4) - Math.pow(tra / 100, 4));
    // heat loss by convection C
    hl6 = fcl * hc * (tcl - ta);

    ts = 0.303 * Math.exp(-0.036 * M) + 0.028;
  
    pmv = ts * (mw - hl1 - hl2 - hl3 - hl4 - hl5 - hl6);
  
   
    return(TwoDec(pmv));
}




/**
 *  Given air temperature (Celsius), relative humidity (%), wind speed (m/sec) and mean radiant temperature ( tmrt in degC) 
 *  gives the Universal Thermal Climate Index in Celsius.
 *  @param {number} t,rh,wind,tmrt
 *  @return {number}
 */

function UTCI(ta,rh,wind,tmrt)  
                 {    
                  
                  var ta,pa,va, e, dtm,i;
                  e = es(ta)/10; // use vapour pressure in kPa 
                  pa = (e*rh/100.0); 
                  va = wind;
	          if (  va < 0.51) {va=0.5;};
	          if (  va > 17) {va=17;};
				 
                  dtm = tmrt - ta;
    
                  utci = new Array(210);
                  
                  utci[0]=ta;
                  utci[1]=6.07562052E-01;
                  utci[2]=-2.27712343E-02*ta;
                  utci[3]=8.06470249E-04*ta*ta;
                  utci[4]=-1.54271372E-04*ta*ta*ta;
                  utci[5]=-3.24651735E-06*ta*ta*ta*ta;
                  utci[6]=7.32602852E-08*ta*ta*ta*ta*ta;
                  utci[7]=1.35959073E-09*ta*ta*ta*ta*ta*ta;
                  utci[8]=-2.25836520E-00*va;
                  utci[9]=8.80326035E-02*ta*va;
                  utci[10]=2.16844454E-03*ta*ta*va;
                  utci[11]=-1.53347087E-05*ta*ta*ta*va;
                  utci[12]=-5.72983704E-07*ta*ta*ta*ta*va;
                  utci[13]=-2.55090145E-09*ta*ta*ta*ta*ta*va;
                  utci[14]=-7.51269505E-01*va*va;
                  utci[15]=-4.08350271E-03*ta*va*va;
                  utci[16]=-5.21670675E-05*ta*ta*va*va;
                  utci[17]=1.94544667E-06*ta*ta*ta*va*va;
                  utci[18]=1.14099531E-08*ta*ta*ta*ta*va*va;
                  utci[19]=1.58137256E-01*va*va*va;
                  utci[20]=-6.57263143E-05*ta*va*va*va;
                  utci[21]=2.22697524E-07*ta*ta*va*va*va;
                  utci[22]=-4.16117031E-08*ta*ta*ta*va*va*va;
                  utci[23]=-1.27762753E-02*va*va*va*va;
                  utci[24]=9.66891875E-06*ta*va*va*va*va;
                  utci[25]=2.52785852E-09*ta*ta*va*va*va*va;
                  utci[26]=4.56306672E-04*va*va*va*va*va;
                  utci[27]=-1.74202546E-07*ta*va*va*va*va*va;
                  utci[28]=-5.91491269E-06*va*va*va*va*va*va;
                  utci[29]=3.98374029E-01*dtm;
                  utci[30]=1.83945314E-04*ta*dtm;
                  utci[31]=-1.73754510E-04*ta*ta*dtm;
                  utci[32]=-7.60781159E-07*ta*ta*ta*dtm;
                  utci[33]=3.77830287E-08*ta*ta*ta*ta*dtm;
                  utci[34]=5.43079673E-10*ta*ta*ta*ta*ta*dtm;
                  utci[35]=-2.00518269E-02*va*dtm;
                  utci[36]=8.92859837E-04*ta*va*dtm;
                  utci[37]=3.45433048E-06*ta*ta*va*dtm;
                  utci[38]=-3.77925774E-07*ta*ta*ta*va*dtm;
                  utci[39]=-1.69699377E-09*ta*ta*ta*ta*va*dtm;
                  utci[40]=1.69992415E-04*va*va*dtm;
                  utci[41]=-4.99204314E-05*ta*va*va*dtm;
                  utci[42]=2.47417178E-07*ta*ta*va*va*dtm;
                  utci[43]=1.07596466E-08*ta*ta*ta*va*va*dtm;
                  utci[44]=8.49242932E-05*va*va*va*dtm;
                  utci[45]=1.35191328E-06*ta*va*va*va*dtm;
                  utci[46]=-6.21531254E-09*ta*ta*va*va*va*dtm;
                  utci[47]=-4.99410301E-06*va*va*va*va*dtm;
                  utci[48]=-1.89489258E-08*ta*va*va*va*va*dtm;
                  utci[49]=8.15300114E-08*va*va*va*va*va*dtm;
                  utci[50]=7.55043090E-04*dtm*dtm;
                  utci[51]=-5.65095215E-05*ta*dtm*dtm;
                  utci[52]=-4.52166564E-07*ta*ta*dtm*dtm;
                  utci[53]=2.46688878E-08*ta*ta*ta*dtm*dtm;
                  utci[54]=2.42674348E-10*ta*ta*ta*ta*dtm*dtm;
                  utci[55]=1.54547250E-04*va*dtm*dtm;
                  utci[56]=5.24110970E-06*ta*va*dtm*dtm;
                  utci[57]=-8.75874982E-08*ta*ta*va*dtm*dtm;
                  utci[58]=-1.50743064E-09*ta*ta*ta*va*dtm*dtm;
                  utci[59]=-1.56236307E-05*va*va*dtm*dtm;
                  utci[60]=-1.33895614E-07*ta*va*va*dtm*dtm;
                  utci[61]=2.49709824E-09*ta*ta*va*va*dtm*dtm;
                  utci[62]=6.51711721E-07*va*va*va*dtm*dtm;
                  utci[63]=1.94960053E-09*ta*va*va*va*dtm*dtm;
                  utci[64]=-1.00361113E-08*va*va*va*va*dtm*dtm;
                  utci[65]=-1.21206673E-05*dtm*dtm*dtm;
                  utci[66]=-2.18203660E-07*ta*dtm*dtm*dtm;
                  utci[67]=7.51269482E-09*ta*ta*dtm*dtm*dtm;
                  utci[68]=9.79063848E-11*ta*ta*ta*dtm*dtm*dtm;
                  utci[69]=1.25006734E-06*va*dtm*dtm*dtm;
                  utci[70]=-1.81584736E-09*ta*va*dtm*dtm*dtm;
                  utci[71]=-3.52197671E-10*ta*ta*va*dtm*dtm*dtm;
                  utci[72]=-3.36514630E-08*va*va*dtm*dtm*dtm;
                  utci[73]=1.35908359E-10*ta*va*va*dtm*dtm*dtm;
                  utci[74]=4.17032620E-10*va*va*va*dtm*dtm*dtm;
                  utci[75]=-1.30369025E-09*dtm*dtm*dtm*dtm;
                  utci[76]=4.13908461E-10*ta*dtm*dtm*dtm*dtm;
                  utci[77]=9.22652254E-12*ta*ta*dtm*dtm*dtm*dtm;
                  utci[78]=-5.08220384E-09*va*dtm*dtm*dtm*dtm;
                  utci[79]=-2.24730961E-11*ta*va*dtm*dtm*dtm*dtm;
                  utci[80]=1.17139133E-10*va*va*dtm*dtm*dtm*dtm;
                  utci[81]=6.62154879E-10*dtm*dtm*dtm*dtm*dtm;
                  utci[82]=4.03863260E-13*ta*dtm*dtm*dtm*dtm*dtm;
                  utci[83]=1.95087203E-12*va*dtm*dtm*dtm*dtm*dtm;
                  utci[84]=-4.73602469E-12*dtm*dtm*dtm*dtm*dtm*dtm;
                  utci[85]=5.12733497E-00*pa;
                  utci[86]=-3.12788561E-01*ta*pa;
                  utci[87]=-1.96701861E-02*ta*ta*pa;
                  utci[88]=9.99690870E-04*ta*ta*ta*pa;
                  utci[89]=9.51738512E-06*ta*ta*ta*ta*pa;
                  utci[90]=-4.66426341E-07*ta*ta*ta*ta*ta*pa;
                  utci[91]=5.48050612E-01*va*pa;
                  utci[92]=-3.30552823E-03*ta*va*pa;
                  utci[93]=-1.64119440E-03*ta*ta*va*pa;
                  utci[94]=-5.16670694E-06*ta*ta*ta*va*pa;
                  utci[95]=9.52692432E-07*ta*ta*ta*ta*va*pa;
                  utci[96]=-4.29223622E-02*va*va*pa;
                  utci[97]=5.00845667E-03*ta*va*va*pa;
                  utci[98]=1.00601257E-06*ta*ta*va*va*pa;
                  utci[99]=-1.81748644E-06*ta*ta*ta*va*va*pa;
                  utci[100]=-1.25813502E-03*va*va*va*pa;
                  utci[101]=-1.79330391E-04*ta*va*va*va*pa;
                  utci[102]=2.34994441E-06*ta*ta*va*va*va*pa;
                  utci[103]=1.29735808E-04*va*va*va*va*pa;
                  utci[104]=1.29064870E-06*ta*va*va*va*va*pa;
                  utci[105]=-2.28558686E-06*va*va*va*va*va*pa;
                  utci[106]=-3.69476348E-02*dtm*pa;
                  utci[107]=1.62325322E-03*ta*dtm*pa;
                  utci[108]=-3.14279680E-05*ta*ta*dtm*pa;
                  utci[109]=2.59835559E-06*ta*ta*ta*dtm*pa;
                  utci[110]=-4.77136523E-08*ta*ta*ta*ta*dtm*pa;
                  utci[111]=8.64203390E-03*va*dtm*pa;
                  utci[112]=-6.87405181E-04*ta*va*dtm*pa;
                  utci[113]=-9.13863872E-06*ta*ta*va*dtm*pa;
                  utci[114]=5.15916806E-07*ta*ta*ta*va*dtm*pa;
                  utci[115]=-3.59217476E-05*va*va*dtm*pa;
                  utci[116]=3.28696511E-05*ta*va*va*dtm*pa;
                  utci[117]=-7.10542454E-07*ta*ta*va*va*dtm*pa;
                  utci[118]=-1.24382300E-05*va*va*va*dtm*pa;
                  utci[119]=-7.38584400E-09*ta*va*va*va*dtm*pa;
                  utci[120]=2.20609296E-07*va*va*va*va*dtm*pa;
                  utci[121]=-7.32469180E-04*dtm*dtm*pa;
                  utci[122]=-1.87381964E-05*ta*dtm*dtm*pa;
                  utci[123]=4.80925239E-06*ta*ta*dtm*dtm*pa;
                  utci[124]=-8.75492040E-08*ta*ta*ta*dtm*dtm*pa;
                  utci[125]=2.77862930E-05*va*dtm*dtm*pa;
                  utci[126]=-5.06004592E-06*ta*va*dtm*dtm*pa;
                  utci[127]=1.14325367E-07*ta*ta*va*dtm*dtm*pa;
                  utci[128]=2.53016723E-06*va*va*dtm*dtm*pa;
                  utci[129]=-1.72857035E-08*ta*va*va*dtm*dtm*pa;
                  utci[130]=-3.95079398E-08*va*va*va*dtm*dtm*pa;
                  utci[131]=-3.59413173E-07*dtm*dtm*dtm*pa;
                  utci[132]=7.04388046E-07*ta*dtm*dtm*dtm*pa;
                  utci[133]=-1.89309167E-08*ta*ta*dtm*dtm*dtm*pa;
                  utci[134]=-4.79768731E-07*va*dtm*dtm*dtm*pa;
                  utci[135]=7.96079978E-09*ta*va*dtm*dtm*dtm*pa;
                  utci[136]=1.62897058E-09*va*va*dtm*dtm*dtm*pa;
                  utci[137]=3.94367674E-08*dtm*dtm*dtm*dtm*pa;
                  utci[138]=-1.18566247E-09*ta*dtm*dtm*dtm*dtm*pa;
                  utci[139]=3.34678041E-10*va*dtm*dtm*dtm*dtm*pa;
                  utci[140]=-1.15606447E-10*dtm*dtm*dtm*dtm*dtm*pa;
                  utci[141]=-2.80626406E-00*pa*pa;
                  utci[142]=5.48712484E-01*ta*pa*pa;
                  utci[143]=-3.99428410E-03*ta*ta*pa*pa;
                  utci[144]=-9.54009191E-04*ta*ta*ta*pa*pa;
                  utci[145]=1.93090978E-05*ta*ta*ta*ta*pa*pa;
                  utci[146]=-3.08806365E-01*va*pa*pa;
                  utci[147]=1.16952364E-02*ta*va*pa*pa;
                  utci[148]=4.95271903E-04*ta*ta*va*pa*pa;
                  utci[149]=-1.90710882E-05*ta*ta*ta*va*pa*pa;
                  utci[150]=2.10787756E-03*va*va*pa*pa;
                  utci[151]=-6.98445738E-04*ta*va*va*pa*pa;
                  utci[152]=2.30109073E-05*ta*ta*va*va*pa*pa;
                  utci[153]=4.17856590E-04*va*va*va*pa*pa;
                  utci[154]=-1.27043871E-05*ta*va*va*va*pa*pa;
                  utci[155]=-3.04620472E-06*va*va*va*va*pa*pa;
                  utci[156]=5.14507424E-02*dtm*pa*pa;
                  utci[157]=-4.32510997E-03*ta*dtm*pa*pa;
                  utci[158]=8.99281156E-05*ta*ta*dtm*pa*pa;
                  utci[159]=-7.14663943E-07*ta*ta*ta*dtm*pa*pa;
                  utci[160]=-2.66016305E-04*va*dtm*pa*pa;
                  utci[161]=2.63789586E-04*ta*va*dtm*pa*pa;
                  utci[162]=-7.01199003E-06*ta*ta*va*dtm*pa*pa;
                  utci[163]=-1.06823306E-04*va*va*dtm*pa*pa;
                  utci[164]=3.61341136E-06*ta*va*va*dtm*pa*pa;
                  utci[165]=2.29748967E-07*va*va*va*dtm*pa*pa;
                  utci[166]=3.04788893E-04*dtm*dtm*pa*pa;
                  utci[167]=-6.42070836E-05*ta*dtm*dtm*pa*pa;
                  utci[168]=1.16257971E-06*ta*ta*dtm*dtm*pa*pa;
                  utci[169]=7.68023384E-06*va*dtm*dtm*pa*pa;
                  utci[170]=-5.47446896E-07*ta*va*dtm*dtm*pa*pa;
                  utci[171]=-3.59937910E-08*va*va*dtm*dtm*pa*pa;
                  utci[172]=-4.36497725E-06*dtm*dtm*dtm*pa*pa;
                  utci[173]=1.68737969E-07*ta*dtm*dtm*dtm*pa*pa;
                  utci[174]=2.67489271E-08*va*dtm*dtm*dtm*pa*pa;
                  utci[175]=3.23926897E-09*dtm*dtm*dtm*dtm*pa*pa;
                  utci[176]=-3.53874123E-02*pa*pa*pa;
                  utci[177]=-2.21201190E-01*ta*pa*pa*pa;
                  utci[178]=1.55126038E-02*ta*ta*pa*pa*pa;
                  utci[179]=-2.63917279E-04*ta*ta*ta*pa*pa*pa;
                  utci[180]=4.53433455E-02*va*pa*pa*pa;
                  utci[181]=-4.32943862E-03*ta*va*pa*pa*pa;
                  utci[182]=1.45389826E-04*ta*ta*va*pa*pa*pa;
                  utci[183]=2.17508610E-04*va*va*pa*pa*pa;
                  utci[184]=-6.66724702E-05*ta*va*va*pa*pa*pa;
                  utci[185]=3.33217140E-05*va*va*va*pa*pa*pa;
                  utci[186]=-2.26921615E-03*dtm*pa*pa*pa;
                  utci[187]=3.80261982E-04*ta*dtm*pa*pa*pa;
                  utci[188]=-5.45314314E-09*ta*ta*dtm*pa*pa*pa;
                  utci[189]=-7.96355448E-04*va*dtm*pa*pa*pa;
                  utci[190]=2.53458034E-05*ta*va*dtm*pa*pa*pa;
                  utci[191]=-6.31223658E-06*va*va*dtm*pa*pa*pa;
                  utci[192]=3.02122035E-04*dtm*dtm*pa*pa*pa;
                  utci[193]=-4.77403547E-06*ta*dtm*dtm*pa*pa*pa;
                  utci[194]=1.73825715E-06*va*dtm*dtm*pa*pa*pa;
                  utci[195]=-4.09087898E-07*dtm*dtm*dtm*pa*pa*pa;
                  utci[196]=6.14155345E-01*pa*pa*pa*pa;
                  utci[197]=-6.16755931E-02*ta*pa*pa*pa*pa;
                  utci[198]=1.33374846E-03*ta*ta*pa*pa*pa*pa;
                  utci[199]=3.55375387E-03*va*pa*pa*pa*pa;
                  utci[200]=-5.13027851E-04*ta*va*pa*pa*pa*pa;
                  utci[201]=1.02449757E-04*va*va*pa*pa*pa*pa;
                  utci[202]=-1.48526421E-03*dtm*pa*pa*pa*pa;
                  utci[203]=-4.11469183E-05*ta*dtm*pa*pa*pa*pa;
                  utci[204]=-6.80434415E-06*va*dtm*pa*pa*pa*pa;
                  utci[205]=-9.77675906E-06*dtm*dtm*pa*pa*pa*pa;
                  utci[206]=8.82773108E-02*pa*pa*pa*pa*pa;
                  utci[207]=-3.01859306E-03*ta*pa*pa*pa*pa*pa;
                  utci[208]=1.04452989E-03*va*pa*pa*pa*pa*pa;
                  utci[209]=2.47090539E-04*dtm*pa*pa*pa*pa*pa;
                  utci[210]=1.48348065E-03*pa*pa*pa*pa*pa*pa;            
                  
                  var total = 0;

                  for (i = 0, n = utci.length; i < n; ++i)
                      {
                           total = total+utci[i];
                      };

                  if (  ta < -50.0 || ta > 60.0 ) {total=9999};
                  if ( (tmrt < ta-30.0) || (tmrt > ta+70.0 )) {total=9999};
                  if (  rh <= 0.0 || rh >= 100.0 ) {total=9999};
                  return TwoDec(total);
}

/**
 * Given air temperature (Celsius), relative humidity (%) give a heat index in Celsius degree. 
 * References:
 * [1] http://www.wpc.ncep.noaa.gov/html/heatindex.shtml 
 * [2] https://en.wikipedia.org/wiki/Heat_index 
 * [3] http://www.srh.noaa.gov/images/ffc/pdf/ta_htindx.PDF
 * 
 * @param {number} t,rh
 * @return {number}
 * @customfunction
 */

function heatindex(t,rh)
{
  var tf, tf2, ur2, hif;
  tf = C2F(t);
  tf2 = Math.pow(tf, 2.0);
  ur2 = Math.pow(rh, 2.0);
  hif = -42.379 + 2.04901523 * tf + 10.1433127 * rh - 0.22475541 *tf * rh
        - 6.83783 * 0.001* tf2 - 5.481717 * 0.01* ur2 +1.22874 * 0.001* tf2* rh
        + 8.5282 * 0.0001* tf * ur2 -1.99 * 0.000001* tf2* ur2;  
  
  if (t < 44 & t > 27 & rh < 13 )
           {
        return (TwoDec(F2C(hif-((13-rh)/4)*Math.sqrt((17-Mat.abs(tf-95.))/17))));
      }
  
  else if (t < 31 & t > 27 & rh > 85 ) {
        return (TwoDec(F2C(hif-((rh-85)/10) * ((87-tf)/5))));
      }
  

  if (t > 27)
      {
        return (TwoDec(F2C(hif)));
      }
     
  else
      
      {return(TwoDec(F2C(0.5 * (tf + 61.0 + ((tf-68.0) *1.2) + (rh*0.094) ))))};
  
}






function utci_class(t,rh,wind,trad) 
  {
	
  var  utci_v,utci_c;
 
  utci_v=UTCI(t,rh,wind,trad);
  
  if ( utci_v > 46.0)
   {utci_c=10.0;}
  else if (utci_v > 38.0 && utci_v <= 46.0)
    {utci_c=9.0;}
  else if (utci_v > 32.0 && utci_v <= 38.0)
  {utci_c=8.0;}
  else if (utci_v > 26.0 && utci_v <= 32.0)
    {utci_c=7.0;}
  else if (utci_v > 9.0 && utci_v <= 26.0)
    {utci_c=6.0;}
  else if (utci_v > 0.0 && utci_v <= 9.0)
    {utci_c=5.0;}
  else if (utci_v > -13.0 && utci_v <= 0)
  {utci_c=4.0;}
  else if (utci_v > -27.0 && utci_v <= -13.0)
    {utci_c=3.0;}	
  else if (utci_v > -40.0 && utci_v <= -27.0)
    {utci_c=2.0;}
  else if (utci_v <= -40.0)
    {utci_c=1.0;}
  else if (utci_v == 9999)
  {utci_c=9999};

  return utci_c;
}

function utci_class7(t,rh, wind,trad) 
{
	
  var  utci_v,utci_c;
 
  utci_v=UTCI(t,rh,wind,trad);
  
  if ( utci_v > 46.0)
   {utci_c=7.0;}
  else if (utci_v > 38.0 && utci_v <= 46.0)
    {utci_c=7.0;}
  else if (utci_v > 32.0 && utci_v <= 38.0)
  {utci_c=7.0;}
  else if (utci_v > 26.0 && utci_v <= 32.0)
    {utci_c=6.0;}
  else if (utci_v > 16.0 && utci_v <= 26.0)
    {utci_c=6.0;}
  else if (utci_v > 0.0 && utci_v <= 16.0)
    {utci_c=5.0;}
  else if (utci_v > -13.0 && utci_v <= 0)
  {utci_c=4.0;}
  else if (utci_v > -27.0 && utci_v <= -13.0)
    {utci_c=3.0;}	
  else if (utci_v > -40.0 && utci_v <= -27.0)
    {utci_c=2.0;}
  else if (utci_v <= -40.0)
    {utci_c=1.0;}
  else if (utci_v == 9999)
  {utci_c=9999};

  return utci_c;
}
    





/**
 * Given t air temperature (Celsius), rh relative humidity (%), wind velocity in m/s and pair air pessure in hPa  gives
 * Fighter index of thermal stress (FITS). 
 * @param {number} t,rh,wind,pair 
 * @return {number}
 */

function fits_index(t,rh,wind,pair) 
         {
          var fits; 
	  if ( pair === undefined) {pair=1010};
	  if ( wind === undefined) {wind=0.13};
        
          var tw = natural_wetbulb(t,rh,wind,0,0,pair);
	
          fits = 0.83*tw+0.35*t+5.08
          return fits;
}


/**
 * lost_productivity is a function to estimate population heat exposure and impacts on working people
 * @param {number} wbgt,tresh
 * @return {number}
 * Estimating population heat exposure and impacts on working people in conjunction with climate change
 * Tord Kjellstrom  & Chris Freyberg & Bruno Lemke & Matthias Otto & David Briggs
 * Int J Biometeorol (2018) 62:291-306 DOI 10.1007/s00484-017-1407-0
*/

function lost_productivity(wbgt,tresh) {  
                                        if( tresh === undefined ) { tresh = 33.5;};
                                        return(0.5*(1+ erf((wbgt-tresh)/(3.75*Math.sqrt(2))))*100)
}

/**
 * Given body mass index  by using antropometric features. 
 * @param {number} h,w
 * @return {number}
 * @customfunction
 */

function BMW(h,w) 
         {return(w/(Math.pow((h/100),2)));} 

/**
 * Given body surface area by using antropometric features height and weigth. 
 * @param {number} h,w
 * @return {number}
 * @customfunction
 */


function BSA(h,w) 
         { return( Math.pow(h/100,0.725)*(0.20247*(Math.pow(w,0.425)))); }    

  
/**
 * Given met rate level by using clothing iso level and BSA.
 * @param {number} BSA, isolevel
 * @return {number}
 */


function met_rate(BSA, isolevel) {
  
   if ( isolevel === undefined) {isolevel = 1 };
  
   return(BSA*(isolevel*50));
}



/**
 * Given met gives acclimated threshold of risk by using wbgt index. 
 * Reference Ergonomics of the thermal environment – Assessment of heat stress using the WBGT (wet bulb globe temperature)  * index, ISO FDIS 7243 (2016)
 * @param {number} met
 * @return {number}
 */

function rel_acclimatized(met) {
  
    
     return(56.7-(11.5*getBaseLog(10,met)));
}


/**
 * Given met gives unacclimated threshold of risk by using wbgt index. 
 * Reference Ergonomics of the thermal environment – Assessment of heat stress using the WBGT (wet bulb globe temperature)  * index, ISO FDIS 7243 (2016)
 * @param {number} met
 * @return {number}
 */

function ral_unacclimatized(met) {
   
     return(59.9-(14.1*getBaseLog(10,met)));
}



          
          
/**
 * Given  WBGT returns heat risk level in italian language by using a treshshold.
 * Reference Ergonomics of the thermal environment – Assessment of heat stress using the WBGT (wet bulb globe temperature) index,ISO FDIS 7243 (2016)
 * @param {number} wbgt,tresh
 * @return {number}
 */

function heat_risk_text_level(wbgt,cav,tresh)  { 
                                               if ( tresh === undefined) {tresh = 28.5 };
                                               var risk= (wbgt+cav)/tresh;
                                               var level_list=["NON SIGNIFICATIVO","BASSO","MODERATO","ALTO"];  
                                               var class;
                                               if    ( risk <= 0.8)        {  class = 0;} 
                                                     else if (risk <= 1)   {  class = 1;} 
                                                     else if (risk <= 1.2) {  class = 2;} 
                                                     else                  {  class = 3};
                                              
                                               return(level_list[class]);           
                                              }

/**
 * Given  WBGT returns heat risk level in english language by using a treshshold.
 * Reference Ergonomics of the thermal environment – Assessment of heat stress using the WBGT (wet bulb globe temperature)  * index, ISO FDIS 7243 (2016)
 * @param {number} wbgt,tresh
 * @return {number}
 */

function heat_risk_text_level_eng(wbgt,cav,tresh)  { 
                                               if ( tresh === undefined) {tresh = 28.5};
                                               var risk= (wbgt+cav)/tresh;
                                               var level_list=["NOT SIGNIFICANT","LOW","MODERATE","HIGH"];  
                                               var class;
                                               if    ( risk <= 0.8)        {  class = 0;} 
                                                     else if (risk <= 1)   {  class = 1;} 
                                                     else if (risk <= 1.2) {  class = 2;} 
                                                     else                  {  class = 3};
                                              
                                               return(level_list[class]);           
                                              }

/**
 * Given  WBGT returns heat risk level as color code.
 * https://www.rapidtables.com/convert/color/hex-to-rgb.html
 * RISCHIO = 80% NESSUN RISCHIO (GREEN) rgb(0,255,0)
 * 80% < RISCHIO = 100% ATTENZIONE (YELLOW) rgb(255,255,0)
 * 100% < RISCHIO = 120% ALLARME (ORANGE) rgb(255,165,0)
 * RISCHIO > 120% EMERGENZA (RED) rgb(255,0,0)
 * @param {number} wbgt,tresh
 * @return {text}
 */
        
  

function heat_risk_color_level(wbgt,cav,tresh)    { 
                                               if ( tresh === undefined) {tresh = 28.5 };
                                               var risk= (wbgt+cav)/tresh;
                                               var colorcode_list=["green","yellow","orange","red"]; 
                                                  var class;
                                               if    ( risk <= 0.8)        {  class = 0;} 
                                                     else if (risk <= 1)   {  class = 1;} 
                                                     else if (risk <= 1.2) {  class = 2;} 
                                                     else                  {  class = 3};
                                               return(colorcode_list[class]);           
                                              }

/**
 *  Given  WBGT and CAV returns heat risk level as color code in hex format. 
 *  @param {number} wbgt,tresh
 *  RISCHIO = 80% NESSUN RISCHIO (GREEN) rgb(0,255,0) level 1 
 *  80% < RISCHIO = 100% ATTENZIONE (YELLOW) rgb(255,255,0) level 2 
 *  100% < RISCHIO = 120% ALLARME (ORANGE) rgb(255,165,0) level 3 
 *  RISCHIO > 120% EMERGENZA (RED) rgb(255,0,0) level 4 
 *  @return {text}
 */

function heat_risk_hexrgb_level(wbgt,cav,tresh)    { 
                                               if ( tresh === undefined) {tresh = 28.5};
                                               var risk= (wbgt+cav)/tresh;
                                               var colorcode_hex=["#00ff00","#ffff00","#ffa500","#ff0000"];
                                               var class;
                                   
                                               if    ( risk <= 0.8)        {  class = 0;} 
                                                     else if (risk <= 1)   {  class = 1;} 
                                                     else if (risk <= 1.2) {  class = 2;} 
                                                     else                  {  class = 3};


                                               return(colorcode_hex[class]);           
                                              }

/**
 *  Given WBGT returns heat risk level value. 
 *  Reference Ergonomics of the thermal environment – Assessment of heat stress using the WBGT 
 *  (wet bulb globe temperature) index,ISO FDIS 7243 (2016)
 *  @param {number} wbgt,cav,tresh
 *  @return {number}
 */

function heat_risk_index_value(wbgt,cav,tresh)    { 
                                               if ( tresh === undefined) {tresh = 28.5};
                                               var risk =((wbgt+cav)/tresh);
                                               return(risk);        
                                              }



/**
 *  Given t air temperature (Celsius degrees), rh relative humidity (%) , wind speed in m per second, 
 *  solar global radiation in  Watt/mq, tg globometric temperature gives, solar zenith in radians,  
 *  pair Air Pressure in millibar (hPa),alb_sfc mean albedo surface, fdir is the ratio between diffuse  
 *  and directed radiation, irad is 1 if the radiation is computed, diam is the diameter of heat globe,
 *  maxair and minair are  *  the range respect to air temperature 
 *  to search solution and prec is the precision the function gives Wet-bulb globe temperature (WBGT)
 *  index following the Liljegren scheme . 
 *  @param {number} t,rh,wind,solar,zenith,pair,alb_sfc,fdir,irad,diam,maxair,minair,prec
 *  @return {number} 
 */

function wbgt_sun(t,rh,wind,solar,zenith,pair,alb_sfc,fdir,irad,diam,maxair,minair,prec) 
          {
          var wbgt;
          if ( pair === undefined ) {pair = 1010;};
          if ( alb_sfc === undefined ) {alb_sfc = 0.4;};
          if ( fdir === undefined ) { fdir = 0.8;}; 
          if ( irad === undefined ) {irad = 1;};
          if ( diam === undefined ) {diam=0.05;};
	        if ( maxair === undefined ) {maxair=10;};
          if ( minair === undefined ) {minair=2;};
          if(  prec === undefined ) {prec=0.01;};
          
          var tg= tglob_sphere(t,rh,wind,solar,zenith,pair,maxair,minair,alb_sfc,fdir,diam,prec);
          var tw = natural_wetbulb(t,rh,wind,solar,zenith,pair,alb_sfc,fdir,irad,prec);
	  	 
          wbgt = 0.7*tw + 0.2*tg+0.1*t;
           
	        if ( solar === undefined  && zenith === undefined ) {wbgt = 0.7 * tw +0.3*t;};
          	 
          return wbgt;
}

/**
 *  Given t air temperature (Celsius degrees), rh relative humidity (%) , wind speed in m/s, 
 *  pair Air Pressure in millibar (hPa),alb_sfc mean albedo surface, fdir is the ratio between 
 *  diffuse and directed radiation, 
 *  irad is 1 if the radiation is computed, diam is the diameter of heat globe, maxair and  
 *  minair are the range, respect to air temperature, where solution was searched.
 *  and prec is the precision.
 *  @param {number} t, rh, wind, pair, alb_sfc, fdir, diam, prec
 *  @return {number}

 */

function wbgt_shade(t,rh,wind,pair,alb_sfc,fdir,diam,prec) 
         {
          var wbgt;
          if( pair === undefined )    {pair = 1010;};
          if( alb_sfc === undefined ) {alb_sfc = 0.4;};
          if( fdir === undefined )    {fdir = 0.8;}; 
          if( diam === undefined )    {diam=0.05;};
          if( prec=== undefined )     {diam=0.1;};
          var tw = natural_wetbulb(t,rh,wind,0.001,0.0001,pair,alb_sfc,fdir,1,prec);
          wbgt = 0.7*tw+0.3*t;
          return wbgt;
}



/**
 * Given t air temperature (degC), rh relative humidity (%) , wind in m/s and pair air pressure  (hPa) 
 * and elevation in meters gives   gives  Wet-bulb globe temperature (WBGT) index indoor.  * Bernard Integration for wind.  * Refernce: Bernard TE, Pourmoghani M (1999)  "Prediction of Workplace Wet Bulb Global Temperature" in    
 * Applied Occupational and Environmental Hygiene 14: 126-134
 * Ramsey JD, Bernard TE (2000) Heat Stress in R Harris (ed) Patty's Industrial Hygiene and Toxicology
 * vol 2 New York:John Wiley & Sons 
 * @param {number} t, rh, wind, pair, elev
 * @return {number} wbgt

 */

function wbgt_indoor(t,rh,wind,pair,elev) 
         {
          if ( wind === undefined) {wind=0.13};
          if ( pair === undefined) {pair=1010};
          if ( elev === undefined) {elev=0};
          
          var wbgt;
          var pair=pheight(pair,elev);
          var tw = natural_wetbulb(t,rh,wind,0,0,pair);
	        wbgt= 0.67*tw+0.33*t-0.048 *Math.log(wind)*(t-tw);
          if ( wind < 1.1) { wbgt= 0.04*t + 0.96*tw};
          return wbgt;
}





/**
 * Given Ambient Air Temperature (< +10 Celsius) and relative air velocity wind ( 0.4 to 18 m/s)
 * give a windchill index - ISO11079. 
 * Reference: http://www.eat.lth.se/fileadmin/eat/Termisk_miljoe/IREQ2009ver4_2.html
 * @param {number} t,wind
 * @return {number}
 */

function windchill(t, wind) 
        { if (wind === undefined ) ( wind=1.3);
          if (wind < 1.3) ( wind = 1.3);
	        wind=(3.6)*wind;
	        var twc = 13.12 + 0.6215 * t-11.37 * Math.pow(wind,0.16) +0.3965 * t* Math.pow(wind,0.16);
	       return(twc);
        }


/**
 * Given Ambient Air Temperature t (<+10 degC) and relative air velocity wind (0.4 to 18 m/s)
 * give a windchill index - ISO11079 in watt on mq. 
 * Reference: http://www.eat.lth.se/fileadmin/eat/Termisk_miljoe/IREQ2009ver4_2.html
 * @param {number} t,wind
 * @return {number}
 */

function wc_watt2mq (t, wind)
			{
			 if (wind < 0.4) ( wind=0.4);
	                 var Watts = (12.1452 + 11.6222*Math.sqrt(wind) - 1.16222 * wind)*(33 - t);
			 return Watts;

			}



/**
 * Given a temperature t (degC ) and wind ( m/sec) frost time following Wind chill class .
 * @param {number} t, wind
 * @return {number} 
 */

function windchill_cla(t,wind)
{    if (wind === undefined ) ( wind=1.3);
     if (wind < 1.3) ( wind=1.3);
	      
     var wcla;
     var wcindex=windchill(t,wind);  
     if (wcindex > 0 ) {return 1;}
     else if (wcindex > -10.0) {return 2;}
     else if (wcindex > -28.0) {return 3;}
     else if (wcindex > -40.0) {return 4;}
     else if (wcindex > -48.0) {return 5;}
     else if (wcindex > -54.0) {return 6;}
     else { return 7;};
}


/**
 * Given a temperature t (degC ) and wind ( m/sec) frost time following Wind chill chart.
 * @param {number} t
 * @return {number} 
 */

function frostime(t,wind)
{
var ft;

if (wind> 100.1|| wind < 0.0)
    return 9999;
else if (t > -10.0 || t < -60.0)
    return 9999;
else{  
     ft=(((-24.5*((0.667*wind)+4.8)+2111)*(Math.pow((-t-4.8),-1.668)))/60);
    }
return OneDec(ft*60);
}

/**
 * Given air temperature (degC), relative humidity (%) and wind (m/s) velocity give Net  
 * effective Index  in degC.
 * @param {number} t,rh
 * @return {number}
 */

function net_index(t, rh, wind)
{
    var net = 9999;
    if (rh > 100.1 || rh < 0.0)
       {return 9999}
    else if (wind > 130.0 || wind < 0.0)
       {return 9999}
    else if (t > 100.0 || t < -100.0)
       {return 9999}
    else
       {net = 37-((37-t)/(0.68-(0.0014*rh)+(1/(1.76+(1.4*(Math.pow(wind,0.75)))))))-(0.29*t*(1.0-(0.01*rh)))}
    return TwoDec(net);
}




/**
 * Given air temperature (Celsius), relative humidity (%) give Summer Simmer Index  in degC.
 *
 * @param {number} t,rh
 * @return {number}
 */

function ssi_index(t,rh)
{  
    var ssi = 9999;
    if (rh > 100.1 || rh < 0.0)
       {return ssi}
    else if (t > 100.0 || t < -100.0)
       {return ssi}
    else
       {ssi = ((1.98*((((9.0/5.0)*t)+32.0)-(0.55-0.0055*rh)*((((9.0/5.0)*t)+32.0)-58.0))-56.83)-32.0)/1.8}
    return  TwoDec(ssi);
}


////////////////////////////////////////////////////////////////////////////////////////////////
// Pressure 


/**
 * Given press air pressure in millibar, topo is altitude in meters 
 * and mean temperature of the air column calculate the local value of pressure
 * @param {number} press,topo,temp
 * @return {number}
 */

function p_local(press,topo,temp)

{    var T0;
     if ( temp === undefined) { temp= 15.0};
     var temp=temp+273.15;        // Formula isometrica di Laplace
     var L=-0.0065;               // temperature lapse rate L = -0.0065 K/m
     var R_cost=287.05 ;          // gas constant for dry air, J/(kg*degK) = 287.05
     var T0=temp-(L/2)*topo;      // sea level standard temperature T0 = 288.15 K
     var p_local= press*Math.exp(-topo*9.81/(R_cost*T0));
     return p_local; 
 
 }


function pheight(press,topo)

{
  var pressalt;
  pressalt= press * Math.pow(1-(2.25577*(0.00001)*topo),5.25588);
  return(pressalt);
}

/**
 * Given t air temperature, rh relative humidity (%), p local air pressure give partial pressure of oxygen.
 *
 * @param {number} t,rh,g
 * @return {number}
 */

function poda(t,rh,p)
 {
  
  var poda;
  var  vpa = (rh / 100) * 6.105 * Math.pow(2.718281828, ( 17.27*t / ( 237.7 + t ) ));
  poda = 80.51 * p / (t + 273.15) * (1.0 - vpa / p);
  return poda;
}


/**
 * Given air temperature (degC) calculates Saturated Vapor Pressure (Torr) at Temperature T  (C) .
 * @param {number} t
 * @return {number}
 */
	
  
function vpaTorr(t) {
    
                     return Math.exp(18.6686 - 4030.183 / (t + 235.0));
}



////////////////////////////////////////////////////////////////////////////////////////////////
