#!/usr/bin/perl
#-------------------------------------------------------
# Build a changelog file for a CVS project
# Serveral output format are available
#-------------------------------------------------------
# $Revision$ - $Author$ - $Date$
use strict; no strict "refs";
use Time::Local;
#use diagnostics;


#-------------------------------------------------------
# Defines
#-------------------------------------------------------
my $REVISION='$Revision$'; $REVISION =~ /\s(.*)\s/; $REVISION=$1;
my $VERSION="2.0 (build $REVISION)";

# ---------- Init variables --------
use vars qw/ $TagStart $Branch $TagEnd /;
my $Debug=0;
my $DIR;
my $PROG;
my $Extension;
my $Help='';
my $TagStart='';
my $TagEnd='';
my $Module='';
my $Output='';		# Default will be "listdeltabydate"
my $CvsRoot='';		# Example ":ntserver:127.0.0.1:d:/temp/cvs"
my $UseSsh=0;
my $RLogFile;
my $RepositoryPath;
my $nowtime = my $nowweekofmonth = my $nowdaymod = my $nowsmallyear = 0; 
my $nowsec = my $nowmin = my $nowhour = my $nowday = my $nowmonth = my $nowyear = my $nowwday = 0;
my $filename='';
my %filesym=();
my $fileformat='';
my $filerevision='';
my $filedate='';
my $fileauthor='';
my $filestate='';
my $filechange='';
my $filelineadd=0;
my $filelinedel=0;
my $filelinechange=0;
my $filelog='';
my $oldfiledayauthor='';
my $oldfilelog='';
my $EXTRACTFILENAME="^RCS file: (.+)";
my $EXTRACTSYMBOLICNAMEAREA="symbolic names:";
my $EXTRACTSYMBOLICNAMEENTRY="^\\s(.+): ([\\d\\.]+)";
my $EXTRACTFILEVERSION="^revision (.+)";
my $EXTRACTFILEDATEAUTHORSTATE="date: (.+)\\sauthor: (.*)\\sstate: ([^\\s]+)(.*)";
my $CVSCLIENT="cvs";
my $COMP="";    # Do no use compression because returned bugged rlog files for some servers/clients.
my $ViewCvsUrl="";
my $ENABLEREQUESTFORADD=1;
# ---------- Init Regex --------
use vars qw/ $regclean1 $regclean2 /;
$regclean1=qr/<(recnb|\/td)>/i;
$regclean2=qr/<\/?[^<>]+>/i;
# ---------- Init hash arrays --------
# For all
my %maxincludedver=();
my %minexcludedver=();
my %Cache=();
# For output by date
my %DateAuthor=();
my %DateAuthorLog=();
my %DateAuthorLogFileRevState=();
my %DateAuthorLogFileRevLine=();
my %HourAuthor=();
# For output by file
my %FilesLastVersion=();
my %FilesChangeDate=();
my %FilesChangeAuthor=();
my %FilesChangeState=();
my %FilesChangeLog=();
# For output by log
my $LGMAXLOG=400;
my %LogChange=();
my %LogChangeDate=();
my %LogChangeAuthor=();
my %LogChangeState=();
# For output by author
my %AuthorChangeCommit=();
my %AuthorChangeLast=();
my %AuthorChangeLineAdd=();
my %AuthorChangeLineDel=();
my %AuthorChangeLineChange=();
# For html report output
my $MAXLASTLOG=500;


#-------------------------------------------------------
# Functions
#-------------------------------------------------------

#-------------------------------------------------------
# Error
#-------------------------------------------------------
sub error {
	print STDERR "Error: $_[0]\n";
    exit 1;
}

#-------------------------------------------------------
# Debug
#-------------------------------------------------------
sub debug {
	my $level = $_[1] || 1;
	if ($Debug >= $level) { 
		my $debugstring = $_[0];
		if ($ENV{"GATEWAY_INTERFACE"}) { $debugstring =~ s/^ /&nbsp&nbsp /; $debugstring .= "<br>"; }
		print STDERR "DEBUG $level - ".time." : $debugstring\n";
		}
	0;
}

#-------------------------------------------------------
# Write
#-------------------------------------------------------
sub writeoutput {
    my $string=shift;
    my $screenonly=shift;
    print STDERR $string;
	0;
}


#-------------------------------------------------------
# LoadDataInMemory
# Load cache entries in Hash
#-------------------------------------------------------
sub LoadDataInMemory {

	# Define filename
	#my $newfilename=ExcludeRepositoryFromPath("$filename");
	my $newfilename=$filename;

	# Define filelog
	my $newfilelog="$filelog";
	$newfilelog =~ s/\n\s*\n/\n/g;					# Remove blank lines

	# DEFINE CHANGE STATUS (removed, changed or added) OF FILE
	my $newfilestate='';
	if ($Output =~ /^listdelta/ || $Output =~ /^buildhtmlreport/) {
		if ($Branch) {
			# We want a delta in a secondary BRANCH: Change status can't be defined
			if (!$filesym{$filename}{$Branch}) { return; }		# This entry is not in branch 
			$newfilestate="unknown";
		}
		else {
			# We want a delta in main BRANCH
			if ($TagStart && $filesym{$filename}{$TagStart}) {
				# File did exist at the beginning
				if ($TagEnd && ! $filesym{$filename}{$TagEnd}) {	# File was removed between TagStart and TagEnd
					$newfilestate="removed";
				}
				else {
					if ($filestate !~ /dead/) {
						$newfilestate="changed";
					}
					else {
						$newfilestate="removed";
					}
				}
			}
			else {
				# File did not exist at the beginning
				if (! $TagEnd || $filesym{$filename}{$TagEnd}) {		# File was added after TagStart (and before TagEnd)
					# If file contains Attic, this means it was removed so, as it didn't exists in start tag version,
					# this means we can ignore this file.
					if ($filename =~ /[\\\/]Attic([\\\/][^\\\/]+)/) { return; }
					if ($filestate !~ /dead/) {
						if ($filechange) {
							$newfilestate="changed";	# Sometimes it should be "added" (if added after a remove). This will be corrected later.
						}
						else {	# A file added after TagStart
							$newfilestate="added";
						}
					}
					else {
						$newfilestate="removed";
					}
				}
				else {
					$newfilestate="removed";
					return;
				}
			}
		}
	}
	# We know state
	# If added or removed, value for lines added and deleted is not correct, so we download file to count it
    if ($Output =~ /^buildhtmlreport/ && $newfilestate eq 'added' && $fileformat ne 'b' && $ENABLEREQUESTFORADD) {
        my $nbline=0;
	    my $relativefilename=ExcludeRepositoryFromPath("$filename");
        if (! defined $Cache{$relativefilename}{$filerevision}) {
            # If number of file not available in cache file
	        my $command="$CVSCLIENT $COMP -d ".$ENV{"CVSROOT"}." update -p -r $filerevision $relativefilename";
	        debug("Getting file $filename revision $filerevision\n",2);
	        debug("with command '$command'\n",2);
            my $pid = open(PH, "$command 2>&1 |");
            while (<PH>) {
                #chomp $_; s/\r$//;
                #debug($_);
                $nbline++;
            }   
            debug("Nb of line : $nbline",2);
            # Save result in a cache for other run
            print CACHE "$relativefilename $filerevision $nbline $fileformat\n";
        }
        else {
            $nbline=$Cache{$relativefilename}{$filerevision};
        }
        print STDERR ".";
        $filechange="+$nbline -0";
        $filelineadd=$nbline;
	}
	
	# All infos were found. We can process record
	debug(">>>> File revision: $fileformat - $newfilename - $filerevision - $filedate - $fileauthor - $filestate - $filelineadd - $filelinechange - $filelinedel - $filechange => $newfilestate",2);
	
	# For output by date
	if ($Output =~ /bydate/ || $Output =~ /forrpm/ || $Output =~ /buildhtmlreport/) {
		$filedate=~/(\d\d\d\d\d\d\d\d)\s(\d\d)/;
		my $fileday=$1;
		my $filehour=$2;
		$HourAuthor{"$filehour $fileauthor"}++;
		$DateAuthor{"$fileday $fileauthor"}++;
		$DateAuthorLog{"$fileday $fileauthor"}{$newfilelog}++;
		$DateAuthorLogFileRevState{"$fileday $fileauthor"}{$newfilelog}{"$newfilename $filerevision"}=$newfilestate;
		if ($newfilestate eq 'removed') {
			# Change a state of a revision from "changed" into "added" when previous revision was "removed"
			my $filerevisionnext=$filerevision;
			if ($filerevisionnext =~ /\.(\d+)$/) {
				my $newver=int($1)+1;
				$filerevisionnext =~ s/\.(\d+)$/\.$newver/;
			}
			if ($DateAuthorLogFileRevState{$oldfiledayauthor}{$oldfilelog}{"$newfilename $filerevisionnext"} =~ /^changed$/) {
				debug("Correct next version of $newfilename $filerevisionnext ($filerevisionnext should be 'added_forced' instead of 'changed')",3);
				$DateAuthorLogFileRevState{$oldfiledayauthor}{$oldfilelog}{"$newfilename $filerevisionnext"}="added_forced";
			}
		}
		# When a version file does not exists in end, all versions are at state 'removed'.
		# We must change this into "changed" for those whose next revision exists and is 'removed'. Only last one stay 'removed'.
		if ($newfilestate eq 'removed') {
			my $filerevisionnext=$filerevision;
			if ($filerevisionnext =~ /\.(\d+)$/) {
				my $newver=int($1)+1;
				$filerevisionnext =~ s/\.(\d+)$/\.$newver/;
			}
			if ($DateAuthorLogFileRevState{$oldfiledayauthor}{$oldfilelog}{"$newfilename $filerevisionnext"} =~ /^(removed|changed_forced)$/) {
				debug("Correct version of $newfilename $filerevision ($filerevision should be 'changed_forced' instead of 'removed')",3);
				$DateAuthorLogFileRevState{"$fileday $fileauthor"}{$newfilelog}{"$newfilename $filerevision"}='changed_forced';	# with _forced to not be change again by previous test
			}
		}
		# Var used to retrieve easily the revision already read just before the one processed in this function
		$oldfiledayauthor="$fileday $fileauthor";
		$oldfilelog="$newfilelog";

		my $filechangebis=$filechange; $filechangebis=~s/\-/ \-/;
		if ($fileformat ne 'b') {
		    $DateAuthorLogFileRevLine{"$fileday $fileauthor"}{$newfilelog}{"$newfilename $filerevision"}=$filechangebis;
		}
		else {
		    $DateAuthorLogFileRevLine{"$fileday $fileauthor"}{$newfilelog}{"$newfilename $filerevision"}='binary';
		}
	}
	
	# For output by file
	if ($Output =~ /byfile/ || $Output =~ /buildhtmlreport/) {
		if (! $FilesLastVersion{$newfilename}) { $FilesLastVersion{$newfilename}=$filerevision; }	# Save 'last' file version
		$FilesChangeDate{$newfilename}{$filerevision}=$filedate;
		$FilesChangeAuthor{$newfilename}{$filerevision}=$fileauthor;
		$FilesChangeState{$newfilename}{$filerevision}=$newfilestate;
		$FilesChangeLog{$newfilename}{$filerevision}=$newfilelog;
	}
	
	# For output by log
	if ($Output =~ /bylog/ || $Output =~ /buildhtmlreport/) {
		$LogChange{$newfilelog}=1;
		$LogChangeDate{$newfilelog}{"$newfilename $filerevision"}=$filedate;
		$LogChangeAuthor{$newfilelog}{"$newfilename $filerevision"}=$fileauthor;
		$LogChangeState{$newfilelog}{"$newfilename $filerevision"}=$newfilestate;
	}
	
	if ($Output =~ /^buildhtmlreport/) {
	    if (! $AuthorChangeLast{$fileauthor} || int($AuthorChangeLast{$fileauthor}) < int($filedate)) { $AuthorChangeLast{$fileauthor}=$filedate; }
	    $AuthorChangeCommit{$fileauthor}{$filename}++;
	    if ($fileformat ne 'b') {
	        $AuthorChangeLineAdd{$fileauthor}+=$filelineadd;
	        $AuthorChangeLineDel{$fileauthor}+=$filelinedel;
	        $AuthorChangeLineChange{$fileauthor}+=$filelinechange;
	    }
	}
}

#------------------------------------------------------------------------------
# Function:     Clean tags in a string
# Parameters:   stringtodecode
# Input:        None
# Output:       None
# Return:		decodedstring
#------------------------------------------------------------------------------
sub CleanFromTags {
	my $stringtoclean=shift;
	$stringtoclean =~ s/$regclean1/ /g;	# Replace <recnb> or </td> with space
	$stringtoclean =~ s/$regclean2//g;	# Remove <xxx>
	return $stringtoclean;
}

#------------------------------------------------------------------------------
# Function:      Format a date
# Input:         String "YYYYMMDD HH:MM:SS xxx"
#                Option "" or "rpm"
# Return:        string "YYYY-MM-DD HH:MM:SS xxx" if option is ""
#                String "Thu Mar 7 2002 xxx" if option is "rpm"
#                String "YYYY-MM-DD HH:MM" if option is "simple"
#------------------------------------------------------------------------------
sub FormatDate {
	my $string=shift;
	my $option=shift;
	if ($option eq 'rpm' && $string =~ /(\d\d\d\d)(\d\d)(\d\d)/) {
		my $ns=Time::Local::timelocal(0,0,0,$3,$2-1,$1);
		my $ctime=localtime($ns); $ctime =~ s/ 00:00:00//;
		$string =~ s/(\d\d\d\d)(\d\d)(\d\d)/$ctime/;
	}
	elsif ($option eq 'simple' && $string =~ /(\d\d\d\d)(\d\d)(\d\d)\s(\d\d):(\d\d)/) {
        $string="$1-$2-$3 $4:$5";
	}
    elsif ($string =~ /(\d\d\d\d)(\d\d)(\d\d)/) {
        $string="$1-$2-$3";
    }
	return "$string";
}

#------------------------------------------------------------------------------
# Function:      Format a state string with color
#------------------------------------------------------------------------------
sub FormatState {
	my $string=shift;
	my %colorstate=('added'=>'#008822','changed'=>'#888888','removed'=>'#880000');
    return "<font color=\"".$colorstate{$string}."\">$string</font>";
}

#------------------------------------------------------------------------------
# Function:      Format a diff link
#------------------------------------------------------------------------------
sub FormatDiffLink {
	my $url=shift;
	my $version=shift;
    my $string='';
    if ($ViewCvsUrl) { $string="$ViewCvsUrl"; }
    $string.="$url";
    if ($ViewCvsUrl) { 
        if (CompareVersionBis($version,"1.1")>0) {
            $string.=".diff?r1=";
            $string.="&r2=".$version;
        }
        else {
            $string.="?rev=".$version;
        }    
    	return "<a href=\"$string\">$url</a>";
	}
	else {
	    return "$string";   
	}
}

#------------------------------------------------------------------------------
# Function:      Format a number
# Input:         number precision
# Return:        dd.d
#                String "Thu Mar 7 2002 xxx" if option is "rpm"
#                String "YYYY-MM-DD HH:MM" if option is "simple"
#------------------------------------------------------------------------------
sub RoundNumber {
	my $number=shift;
	my $precision=shift;
    foreach (1..$precision) { $number*=10; }
    $number=int($number);
    foreach (1..$precision) { $number/=10; }
	return "$number";
}

#------------------------------------------------------------------------------
# Function:      Compare 2 CVS version number
# Input:         $a $b
# Output:        -1 if $a < $b, 1 if $a >= $b
#------------------------------------------------------------------------------
sub CompareVersion {
	my $a=shift;
	my $b=shift;
	my $aint; my $adec; my $bint; my $bdec;
	if ($a =~ /^(\d+)\.(\d+)$/) { $aint=int($1); $adec=int($2); } else { $aint=int($a); $adec=0; }
	if ($b =~ /^(\d+)\.(\d+)$/) { $bint=int($1); $bdec=int($2); } else { $bint=int($b); $bdec=0; }
	if ($aint < $bint) { return -1; }
	if ($aint > $bint) { return 1; }
	if ($adec < $bdec) { return -1; }
	return 1;
}

#------------------------------------------------------------------------------
# Function:      Compare 2 CVS version number
# Input:         $a $b
# Output:        -1 if $a < $b, 0 if $a = $b, 1 if $a > $b
#------------------------------------------------------------------------------
sub CompareVersionBis {
	my $a=shift;
	my $b=shift;
	my $aint; my $adec; my $bint; my $bdec;
	if ($a =~ /^(\d+)\.(\d+)$/) { $aint=int($1); $adec=int($2); } else { $aint=int($a); $adec=0; }
	if ($b =~ /^(\d+)\.(\d+)$/) { $bint=int($1); $bdec=int($2); } else { $bint=int($b); $bdec=0; }
	if ($aint < $bint) { return -1; }
	if ($aint > $bint) { return 1; }
	if ($adec < $bdec) { return -1; }
	if ($adec > $bdec) { return 1; }
	return 0;
}

sub ExcludeRepositoryFromPath {
	my $file=shift;
	$file =~ s/[\\\/]Attic([\\\/][^\\\/]+)/$1/;
	$file =~ s/^.*[\\\/]$Module[\\\/]//;		# Extract path of repository
	return $file;
}

#------------------------------------------------------------------------------
# Function:     Return day of week of a day
# Parameters:	"$year$month$day"
# Return:		1-7 (1 = monday, 7=sunday)
#------------------------------------------------------------------------------
sub DayOfWeek {
	shift =~ /(\d\d\d\d)(\d\d)(\d\d)/;
	my ($day, $month, $year) = ($3, $2, $1);
	if ($Debug) { debug("DayOfWeek for $day $month $year",4); }
	if ($month < 3) {  $month += 10;  $year--; }
	else { $month -= 2; }
	my $cent = sprintf("%1i",($year/100));
	my $y = ($year % 100);
	my $dw = (sprintf("%1i",(2.6*$month)-0.2) + $day + $y + sprintf("%1i",($y/4)) + sprintf("%1i",($cent/4)) - (2*$cent)) % 7;
	$dw += 7 if ($dw<0);
    if (! $dw) { $dw = 7; } # It's sunday
	if ($Debug) { debug(" is $dw",4); }
	return $dw;
}


#-------------------------------------------------------
# MAIN
#-------------------------------------------------------
my $QueryString=''; for (0..@ARGV-1) { $QueryString .= "$ARGV[$_] "; }
if ($QueryString =~ /debug=(\d+)/i)    			{ $Debug=$1; }
if ($QueryString =~ /m(?:odule|)=([^\s]+)/i)	{ $Module=$1; }
if ($QueryString =~ /output=([^\s]+)/i)   		{ $Output=$1; }
if ($QueryString =~ /branch=([^\s]+)/i)			{ $Branch=$1; }
if ($QueryString =~ /tagstart=([^\s]+)/i) 		{ $TagStart=$1; }
if ($QueryString =~ /tagend=([^\s]+)/i)   		{ $TagEnd=$1; }
if ($QueryString =~ /rlogfile=([:\-\.\\\/\wè~]+)/i) { $RLogFile=$1; }
if ($QueryString =~ /-d=([^\s]+)/)      		{ $CvsRoot=$1; }
if ($QueryString =~ /-h/)      					{ $Help=1; }
if ($QueryString =~ /-ssh/)    					{ $UseSsh=1 }
($DIR=$0) =~ s/([^\/\\]*)$//; ($PROG=$1) =~ s/\.([^\.]*)$//; $Extension=$1;
debug("Module: $Module");
debug("Output: $Output");

# On determine chemin complet du repertoire racine et on en deduit les repertoires de travail
my $REPRACINE;
if (! $ENV{"SERVER_NAME"}) {
	$REPRACINE=($DIR?$DIR:".")."/..";
} else {
	$REPRACINE=$ENV{"DOCUMENT_ROOT"};
}

my %param=();
if ($Output) {
    if ($Output =~ s/:(.*)//g) {
        # There is some parameter on output option
        foreach my $key (split(/,/,$1)) { $param{$key}=1; }
        if ($param{'nolimit'}) { $MAXLASTLOG=0; }
    }
	my %allowedvalueforoutput=(
	"listdeltabydate"=>1,
	"listdeltabylog"=>1,
	"listdeltabyfile"=>1,
	"listdeltaforrpm"=>1,
	"buildhtmlreport"=>1
	);
	if (! $allowedvalueforoutput{$Output}) {
		writeoutput("----- $PROG $VERSION (c) Laurent Destailleur -----\n");
		writeoutput("Unknown value for output parameter.\n");
		exit 1;
	}
}

if ($Help || ! $Output) {
	writeoutput("----- $PROG $VERSION (c) Laurent Destailleur -----\n");
	writeoutput("$PROG generates advanced ChangeLog/Report files for CVS projects/modules.\n");
	writeoutput("Note 1: Your cvs client (cvs or cvs.exe) must be in your PATH.\n");
	writeoutput("Note 2: To use $PROG with a csv client through ssh, add option -ssh.\n");
	writeoutput("\nUsage:\n");
	writeoutput("  $PROG.$Extension -output=outputmode [-m=module -d=repository] [options]\n");
	writeoutput("\n");
	writeoutput("Where 'outputmode' is:\n");
	writeoutput("  listdeltabydate  To get a changelog between 2 versions, sorted by date\n");
	writeoutput("  listdeltabylog   To get a changelog between 2 versions, sorted by log\n");
	writeoutput("  listdeltabyfile  To get a changelog between 2 versions, sorted by file\n");
	writeoutput("  listdeltaforrpm  To get a changelog between 2 versions for rpm spec files\n");
	writeoutput("  buildhtmlreport  To build an html report\n");
	writeoutput("\n");
	writeoutput("  Note that \"between 2 versions\" means (depends on tagstart/tagend options):\n");
	writeoutput("  * from start to a tagged version (version changes included)\n");
	writeoutput("  * from a start version (excluded) to another tagged version (included)\n");
	writeoutput("  * or from a tagged version until now (version changes excluded)\n");
	writeoutput("\n");
	writeoutput("The 'module' and 'repository' are the CVS module name and the CVS repository.\n");
	writeoutput("  If current directory is the root of a CVS project built from a cvs checkout,\n");
	writeoutput("  cvschangelogbuilder will retreive module and repository value automatically.\n");
	writeoutput("  If no local copy of repository are available or to force other value, use:\n");
	writeoutput("  -m=module           To force value of module name\n");
	writeoutput("  -d=repository       To force value of CVSROOT\n");
	writeoutput("\n");
	writeoutput("Options are:\n");
	writeoutput("  -branch=branchname  To work on another branch than default branch (!)\n");
	writeoutput("  -tagstart=tagname   To specify start tag version\n");
	writeoutput("  -tagend=tagend      To specify end tag version\n");
	writeoutput("\n");
	writeoutput("  ! WARNING: If you use tagstart and/or tagend, check that tags are in SAME\n");
	writeoutput("  BRANCH. Also, it must be the default branch, if not, you MUST use -branch to\n");
	writeoutput("  give the name of the branch, otherwise you will get unpredicable result.\n");
	writeoutput("\n");
	writeoutput("  -ssh                To run CVS through ssh (this only set CVS_RSH=\"ssh\")\n");
	writeoutput("  -debug=x            To get debug info with level x\n");
	writeoutput("  -rlogfile=rlogfile  If an up-to-date log file already exist localy, you can use\n");
	writeoutput("                      this option to save on step, for a faster result.\n");
	writeoutput("\n");
	writeoutput("Example:\n");
	writeoutput("  $PROG.$Extension -module=myproject -output=listdeltabyfile -tagstart=myproj_2_0 -d=john\@cvsserver:/cvsdir\n");
	writeoutput("  $PROG.$Extension -module=mymodule  -output=listdeltabydate -d=:ntserver:127.0.0.1:d:/mycvsdir\n");
	writeoutput("  $PROG.$Extension -module=mymodule  -output=listdeltabylog  -d=:pserver:user\@127.0.0.1:/usr/local/cvsroot\n");
	writeoutput("  $PROG.$Extension -module=mymodule  -output=buildhtmlreport -d=:ext:user\@cvs.sourceforge.net:/cvsroot\n");
	writeoutput("\n");
	exit 0;
}

# Get current time
my $nowtime=time;
my ($nowsec,$nowmin,$nowhour,$nowday,$nowmonth,$nowyear) = localtime($nowtime);
if ($nowyear < 100) { $nowyear+=2000; } else { $nowyear+=1900; }
my $nowsmallyear=$nowyear;$nowsmallyear =~ s/^..//;
if (++$nowmonth < 10) { $nowmonth = "0$nowmonth"; }
if ($nowday < 10) { $nowday = "0$nowday"; }
if ($nowhour < 10) { $nowhour = "0$nowhour"; }
if ($nowmin < 10) { $nowmin = "0$nowmin"; }
if ($nowsec < 10) { $nowsec = "0$nowsec"; }
# Get tomorrow time (will be used to discard some record with corrupted date (future date))
my ($tomorrowsec,$tomorrowmin,$tomorrowhour,$tomorrowday,$tomorrowmonth,$tomorrowyear) = localtime($nowtime+86400);
if ($tomorrowyear < 100) { $tomorrowyear+=2000; } else { $tomorrowyear+=1900; }
my $tomorrowsmallyear=$tomorrowyear;$tomorrowsmallyear =~ s/^..//;
if (++$tomorrowmonth < 10) { $tomorrowmonth = "0$tomorrowmonth"; }
if ($tomorrowday < 10) { $tomorrowday = "0$tomorrowday"; }
if ($tomorrowhour < 10) { $tomorrowhour = "0$tomorrowhour"; }
if ($tomorrowmin < 10) { $tomorrowmin = "0$tomorrowmin"; }
if ($tomorrowsec < 10) { $tomorrowsec = "0$tomorrowsec"; }
my $timetomorrow=$tomorrowyear.$tomorrowmonth.$tomorrowday.$tomorrowhour.$tomorrowmin.$tomorrowsec;	

# Check/Retreive module
my $ModuleChoosed=$Module;
if (! $Module || $Output =~ /^buildhtmlreport/) {
    $Module='';
	if (-s "CVS/Repository") {
		open(REPOSITORY,"<CVS/Repository") || error("Failed to open 'CVS/Repository' file to get module name.");
		while (<REPOSITORY>) {
			chomp $_; s/\r$//;
			$Module=$_;
			last;
		}
		close(REPOSITORY);
	}
}
if ($Output =~ /^buildhtmlreport/ && $ModuleChoosed && $Module && $Module ne $ModuleChoosed) {
	writeoutput("\n");
	error("$PROG is launched from a checkout root directory of module '$Module' but you ask a report for module '$ModuleChoosed'.");
}
if (! $Module) {
	writeoutput("\n");
	error("The module name was not provided and could not be detected.\nUse -m=cvsmodulename option to specifiy module name.\n\nExample: $PROG.$Extension -output=$Output -module=mymodule -d=:pserver:user\@127.0.0.1:/usr/local/cvsroot");
}
writeoutput(ucfirst($PROG)." launched for module: $Module\n",1);

# Check/Retreive CVSROOT environment variable (needed only if no option -rlogfile || buildhtmlreport)
if (! $RLogFile || $Output =~ /^buildhtmlreport/) {
	my $CvsRootChoosed=$CvsRoot;
	if (! $CvsRoot || $Output =~ /^buildhtmlreport/) {
		# Try to get CvsRoot from CVS repository
		if (-s "CVS/Root") {
			open(REPOSITORY,"<CVS/Root") || error("Failed to open 'CVS/Root' file to get repository value.");
			while (<REPOSITORY>) {
				chomp $_; s/\r$//;
				$CvsRoot=$_;
				last;
			}
			close(REPOSITORY);
		}
	}
    if ($Output =~ /^buildhtmlreport/ && $CvsRootChoosed && $CvsRoot && $CvsRoot ne $CvsRootChoosed) {
	    writeoutput("\n");
    	error("$PROG is launched from a checkout root directory of module '$Module' with cvsroot '$CvsRoot' but you ask a report ".($ModuleChoosed?"for module '$ModuleChoosed' ":"")."with a different cvsroot '$CvsRootChoosed'.");
    }
	if (! $CvsRoot) {
		# Try to set CvsRoot from CVSROOT environment variable
		if ($ENV{"CVSROOT"}) { $CvsRoot=$ENV{"CVSROOT"}; }
	}
	if (! $CvsRoot) {
		writeoutput("\n");
		error("The repository value to use was not provided and could not be detected.\nUse -d=repository option to specifiy repository value.\n\nExample: $PROG.$Extension -output=$Output -module=mymodule -d=:pserver:user\@127.0.0.1:/usr/local/cvsroot");
	}

	$ENV{"CVSROOT"}=$CvsRoot;
	writeoutput(ucfirst($PROG)." launched for repository: $CvsRoot\n",1);

}


# Set use of ssh or not
if ($UseSsh) {
	writeoutput("Set CVS_RSH=ssh\n",1);
	$ENV{'CVS_RSH'}='ssh';
}

# SUMMARY OF PARAMETERS
#------------------------------------------

# LAUNCH CVS COMMAND RLOG TO WRITE RLOGFILE
#------------------------------------------
if (! $RLogFile) {
    print STDERR "Need to download cvs log file, please wait...\n";
	# Define temporary file
	my $TmpDir="";
	$TmpDir||=$ENV{"TMP"};
	$TmpDir||=$ENV{"TEMP"};
	$TmpDir||='/tmp';
	my $TmpFile="$TmpDir/$PROG.$$.tmp";
	open(TEMPFILE,">$TmpFile") || error("Failed to open temp file '$TmpFile' for writing. Check directory and permissions.");
	my $command;
	#$command="$CVSCLIENT rlog ".($TagStart||$TagEnd?"-r$TagStart:$TagEnd ":"")."$Module";
	if ($Branch) {
		$command="$CVSCLIENT $COMP -d ".$ENV{"CVSROOT"}." rlog -r${Branch} $Module";
	}
	else {
		$command="$CVSCLIENT $COMP -d ".$ENV{"CVSROOT"}." rlog".($TagStart||$TagEnd?" -r${TagStart}::${TagEnd}":"")." $Module";
	}
	writeoutput("Building temporary cvs rlog file '$TmpFile'\n",1);
	writeoutput("with command '$command'\n",1);
	debug("CVSROOT value is '".$ENV{"CVSROOT"}."'");
	my $result=`$command 2>&1`;
	print TEMPFILE "$result";
	close TEMPFILE;
	if ($result !~ /cvs \w+: Logging/i) {		# With log we get 'cvs server: Logging awstats' and with rlog we get 'cvs rlog: Logging awstats'
		error("Failure in cvs command: '$command'\n$result");
	}
	$RLogFile=$TmpFile;
}

# ANALYZE RLOGFILE
#------------------------
writeoutput("Analyzing rlog file '$RLogFile'\n",1);
if ($Output =~ /^buildhtmlreport/) {
    my $cachefile="${PROG}_$Module.cache";
    if (-f $cachefile) {
        writeoutput("Load cache file '$cachefile' with number of lines for added files...\n",1);
        open(CACHE,"<$cachefile") || error("Failed to open cache file '$cachefile' for reading");
        while (<CACHE>) {
            chomp $_; s/\r$//;
            my ($file,$revision,$nbline,undef)=split(/\s+/,$_);
            debug(" Load cache entry for ($file,$revision)=$nbline",2);
            $Cache{$file}{$revision}=$nbline;
        }
        close CACHE;
    } else {
        print STDERR "No cache file yet, so it can takes a long time. Please wait...\n";
    }
    open(CACHE,">>$cachefile") || error("Failed to open cache file '$cachefile' for writing");
}

open(RLOGFILE,"<$RLogFile") || error("Can't open rlog file");
my $waitfor="filename";
while (<RLOGFILE>) {
	chomp $_; s/\r$//;
	my $line="$_";

	debug("Analyze line $line (waitfor=$waitfor)",3);

	# Check if there is a warning in rlog file
	#if ($line =~ /^cvs rlog: warning: no revision/) { print("$line\n"); next; }

	# Wait for a new file
	if ($waitfor eq "filename") {
        #if ($line =~ /^cvs rlog: Logging (.*)/) { $Module=$1; } # Set module name from log file
		if ($line =~ /$EXTRACTFILENAME/i) {
			$filename=$1;
			$filename =~ s/,v$//g;					# Clean filename if ended with ",v"
			# We found a new filename
			$waitfor="symbolic_name";
			debug("Found a new file '$filename'",2);
			#filename=ExcludeRepositoryFromPath($filename);
			$maxincludedver{"$filename"}=0;
			$minexcludedver{"$filename"}=0;
		}
		next;
	}

	# Wait for symbolic names area
	if ($waitfor eq "symbolic_name") {
		if ($line =~ /$EXTRACTSYMBOLICNAMEAREA/i) {
			# We found symbolic names area
			$waitfor="symbolic_name_entry";
			debug("Found symbolic name area",2);
		}
		next;
	}

	# Wait for symbolic names entry
	if ($waitfor eq "symbolic_name_entry") {
		if ($line =~ /$EXTRACTSYMBOLICNAMEENTRY/i) {
			# We found symbolic name entry
			# We set symbolic name. Example: $filesym{$filename}{MYAPPLI_1_0}=1.2
			$filesym{$filename}{$1}=$2;
			debug("Found symbolic name entry $1 is for version $filesym{$filename}{$1}",2);
			if ($TagEnd && $TagEnd eq $1) {
				$maxincludedver{"$filename"}=$2;
				debug(" Max included version for file '$filename' set to $2",3);
			}
			if ($TagStart && $TagStart eq $1) {
				$minexcludedver{"$filename"}=$2;
				debug(" Min excluded version for file '$filename' set to $2",3);
			}
		}
		else {
            if ($line =~ /^keyword substitution: (\S+)/) { $fileformat=$1; }
			$waitfor="revision";
		}
		next;
	}

	# Wait for a revision
	if ($waitfor eq "revision") {
		if ($line =~ /^=====/) {
			# No revision found
			$waitfor="filename";
			debug(" No revision found. Waiting for next $waitfor.",2);
			$fileformat=''; $filedate=''; $fileauthor=''; $filestate=''; $filechange=''; $filelog=''; $filelineadd=0; $filelinedel=0; $filelinechange=0;
			next;	
		}
		if ($line =~ /$EXTRACTFILEVERSION/i) {
			# We found a new revision number
			$filerevision=$1;
			$waitfor="dateauthorstate";
			debug("Found a new revision number $filerevision",2);
		}
		next;
	}

	# Wait for date and author of revision
	if ($waitfor eq "dateauthorstate") {
		if ($line =~ /$EXTRACTFILEDATEAUTHORSTATE/i) {
			# We found date/author line
			$filedate=$1; $fileauthor=$2; $filestate=$3; $filechange=$4;
			$filedate =~ s/\///g;
			$filelineadd=0; $filelinedel=0; $filelinechange=0;
			$filechange =~ s/[^\s\d\+\-]+//g;
			foreach my $key (split(/\s+/,$filechange)) {
			    if (int($key)>0) { $filelineadd=int($key); }
			    if (int($key)<0) { $filelinedel=(-int($key)); }
			}
		    if ($filelineadd>=$filelinedel) { $filelineadd-=$filelinedel; $filelinechange=$filelinedel; $filelinedel=0; }
		    else { $filelinedel-=$filelineadd; $filelinechange=$filelineadd; $filelineadd=0; }
			$filedate =~ s/[\s;]+$//; $fileauthor =~ s/[\s;]+$//; $filestate =~ s/[\s;]+$//; $filechange =~ s/\s+//g;
			$waitfor="log";
			debug("Found a new date/author/state/lines $filedate $fileauthor $filestate $filelineadd $filelinedel $filelinechange",2);
		}
		next;
	}

	# Wait for log comment
	if ($waitfor eq "log") {
		if ($line =~ /^branches:/) { next; }
		if ($line =~ /^-----/) {
			$waitfor="revision";
			LoadDataInMemory();
			debug(" Revision info are stored. Waiting for next $waitfor.",2);
			$filedate=''; $fileauthor=''; $filestate=''; $filechange=''; $filelog=''; $filelineadd=0; $filelinedel=0; $filelinechange=0;
			next;	
		}
		if ($line =~ /^=====/) {
			$waitfor="filename";
			LoadDataInMemory();
			debug(" Revision info are stored. Waiting for next $waitfor.",2);
			$filedate=''; $fileauthor=''; $filestate=''; $filechange=''; $filelog=''; $filelineadd=0; $filelinedel=0; $filelinechange=0;
			next;	
		}
		# Line is log
		debug("Found a new line for log $line",2);
		$filelog.="$line\n";
		next;
	}
}
close RLOGFILE;
if ($Output =~ /^buildhtmlreport/) {
    close CACHE;
}



# BUILD OUTPUT
#------------------------
writeoutput("\nBuild output for option '$Output'\n",1);

# Build header
my $headstring='';
my $rangestring='';
if ($Output !~ /buildhtmlreport$/) {
    $headstring.="\nChanges for $Module";
}
else {
    $headstring.="\nCVS report for module <b>$Module</b>";
}
if ($Branch) {
    $headstring.=" in branch $Branch";
    $rangestring.="Branch $Branch";
}
else {
    $rangestring.="Main Branch (HEAD)";
}
if ($TagStart) {
	if ($TagEnd) {
	    $headstring.=" beetween $TagStart (excluded) and $TagEnd (included)";
	    $rangestring.= " - Beetween $TagStart (excluded) and $TagEnd (included)"; 
	}
	else {
	    $headstring.=" since $TagStart (excluded)";
	    $rangestring.= " - Since $TagStart (excluded)";
	}
}
elsif ($TagEnd) {
	$headstring.=" in $TagEnd";
    $rangestring.= " in $TagEnd";
}
$headstring.="\n built by $PROG $VERSION with option $Output.";
if ($Output !~ /buildhtmlreport$/) {
    print "$headstring\n\n";
}
else {
    print "<html>\n<head>\n";
    print "<meta name=\"generator\" content=\"$PROG $VERSION\" />\n";
    print "<meta name=\"robots\" content=\"noindex,nofollow\" />\n";
    print "<meta http-equiv=\"content-type\" content=\"text/html; charset=iso-8859-1\" />\n";
    print "<meta http-equiv=\"description\" content=\"$headstring\" />\n";
    print "<title>CVS report for $Module</title>\n";
    print <<EOF;
<style type="text/css">
<!--
body { font: 11px verdana, arial, helvetica, sans-serif; background-color: #FFFFFF; margin-top: 0; margin-bottom: 0; }
.aws_bodyl  { }
.aws_border { background-color: #FFE0B0; padding: 1px 1px 1px 1px; margin-top: 0; margin-bottom: 0; }
.aws_title  { font: 13px verdana, arial, helvetica, sans-serif; font-weight: bold; background-color: #FFE0B0; text-align: center; margin-top: 0; margin-bottom: 0; padding: 1px 1px 1px 1px; color: #000000; }
.aws_blank  { font: 13px verdana, arial, helvetica, sans-serif; background-color: #FFE0B0; text-align: center; margin-bottom: 0; padding: 1px 1px 1px 1px; }
.aws_data {
	background-color: #FFFFFF;
	border-top-width: 1px;   
	border-left-width: 0px;  
	border-right-width: 0px; 
	border-bottom-width: 0px;
}
.aws_formfield { font: 13px verdana, arial, helvetica; }
.aws_button {
	font-family: arial,verdana,helvetica, sans-serif;
	font-size: 12px;
	border: 1px solid #ccd7e0;
	background-image : url(/icon/other/button.gif);
}
th		{ border-color: #ECECEC; border-left-width: 0px; border-right-width: 1px; border-top-width: 0px; border-bottom-width: 1px; padding: 1px 2px 1px 1px; font: 11px verdana, arial, helvetica, sans-serif; text-align:center; color: #000000; }
th.aws	{ border-color: #ECECEC; border-left-width: 0px; border-right-width: 1px; border-top-width: 0px; border-bottom-width: 1px; padding: 1px 2px 1px 1px; font-size: 13px; font-weight: bold; }
td		{ border-color: #ECECEC; border-left-width: 0px; border-right-width: 1px; border-top-width: 0px; border-bottom-width: 1px; padding: 1px 1px 1px 1px; font: 11px verdana, arial, helvetica, sans-serif; text-align:center; color: #000000; }
td.aws	{ border-color: #ECECEC; border-left-width: 0px; border-right-width: 1px; border-top-width: 0px; border-bottom-width: 1px; padding: 1px 1px 1px 1px; font: 11px verdana, arial, helvetica, sans-serif; text-align:left; color: #000000; }
td.awsm	{ border-left-width: 0px; border-right-width: 0px; border-top-width: 0px; border-bottom-width: 0px; padding: 0px 0px 0px 0px; font: 11px verdana, arial, helvetica, sans-serif; text-align:left; color: #000000; }
b { font-weight: bold; }
a { font: 11px verdana, arial, helvetica, sans-serif; }
a:link    { color: #0011BB; text-decoration: none; }
a:visited { color: #0011BB; text-decoration: none; }
a:hover   { color: #605040; text-decoration: underline; }
div { font: 12px 'Arial','Verdana','Helvetica', sans-serif; text-align: justify; }
.CTooltip { position:absolute; top: 0px; left: 0px; z-index: 2; width: 380px; visibility:hidden; font: 8pt 'MS Comic Sans','Arial',sans-serif; background-color: #FFFFE6; padding: 8px; border: 1px solid black; }
//-->
</style>
EOF
    print "</head>\n";
    print "<body>\n";
}

# For output by date
if ($Output =~ /bydate$/ || $Output =~ /forrpm$/) {
	if (scalar keys %DateAuthor) {
		foreach my $date (reverse sort keys %DateAuthor) {
			my $firstlineprinted=0;
			foreach my $logcomment (sort keys %{$DateAuthorLog{$date}}) {
				foreach my $revision (sort keys %{$DateAuthorLogFileRevState{$date}{$logcomment}}) {
					$revision=~/(.*)\s([\d\.]+)/;
					my ($file,$version)=($1,$2);
					if ($maxincludedver{"$file"} && (CompareVersionBis($2,$maxincludedver{"$file"}) > 0)) { debug("For file '$file' $2 > maxincludedversion= ".$maxincludedver{"$file"},3); next; }
					if ($minexcludedver{"$file"} && (CompareVersionBis($2,$minexcludedver{"$file"}) <= 0)) { debug("For file '$file' $2 <= minexcludedversion= ".$minexcludedver{"$file"},3); next; }
					if (! $firstlineprinted) {
						if ($Output =~ /forrpm$/) { print "* ".FormatDate($date,'rpm')."\n"; }
						else { print FormatDate($date)."\n"; }
						$firstlineprinted=1;
					}
					my $state=$DateAuthorLogFileRevState{$date}{$logcomment}{$revision};
					$state =~ s/_forced//;
					if ($Output !~ /forrpm$/) {
						print "\t* ".ExcludeRepositoryFromPath($file)." $version ($state):\n";
					}
				}
				chomp $logcomment;
				$logcomment =~ s/\r$//;
				if ($firstlineprinted) {
					foreach my $logline (split(/\n/,$logcomment)) {
						if ($Output =~ /forrpm$/) { print "\t- $logline\n"; }
						else { print "\t\t$logline\n"; }
					}
				}
			}
			if ($firstlineprinted) { print "\n"; }
		}	
	}
	else {
		print "No change detected.\n";	
	}
}

# For output by file
if ($Output =~ /byfile$/) {
	if (scalar keys %FilesLastVersion) {
		foreach my $file (sort keys %FilesLastVersion) {
			my $firstlineprinted=0;
			my $val='';
			foreach my $version (reverse sort { &CompareVersion($a,$b) } keys %{$FilesChangeDate{$file}}) {
				if ($maxincludedver{"$file"} && (CompareVersionBis($version,$maxincludedver{"$file"}) > 0)) { debug("For file '$file' $version > maxincludedversion= ".$maxincludedver{"$file"},3); next; }
				if ($minexcludedver{"$file"} && (CompareVersionBis($version,$minexcludedver{"$file"}) <= 0)) { debug("For file '$file' $version <= minexcludedversion= ".$minexcludedver{"$file"},3); next; }
				if (! $firstlineprinted) {
					print ExcludeRepositoryFromPath($file)."\n";
					$firstlineprinted=1;
				}
				printf ("\t* %-16s ",$version." (".$FilesChangeState{$file}{$version}.")");
				print FormatDate($FilesChangeDate{$file}{$version})."\t$FilesChangeAuthor{$file}{$version}\n";
				my $logcomment=$FilesChangeLog{$file}{$version};
				chomp $logcomment;
				$logcomment =~ s/\r$//;
				if ($firstlineprinted) {
					foreach my $logline (split(/\n/,$logcomment)) {
						print "\t\t$logline\n";
					}
				}
			}
		}	
	}
	else {
		print "No change detected.\n";	
	}
}

# For output by log
if ($Output =~ /bylog$/) {
	if (scalar keys %LogChange) {
		foreach my $logcomment (sort keys %LogChange) {
			my $firstlineprinted=0;
			my $newlogcomment=substr($logcomment,0,$LGMAXLOG);
			if (length($logcomment)>$LGMAXLOG) { $newlogcomment.="..."; }
			foreach my $revision (sort { &CompareVersion($a,$b) } keys %{$LogChangeDate{$logcomment}}) {
				$revision=~/^(.*)\s([\d\.]+)$/;
				my ($file,$version)=($1,$2);
				if ($maxincludedver{"$file"} && (CompareVersionBis($2,$maxincludedver{"$file"}) > 0)) { debug("For file '$file' $2 > maxincludedversion= ".$maxincludedver{"$file"},3); next; }
				if ($minexcludedver{"$file"} && (CompareVersionBis($2,$minexcludedver{"$file"}) <= 0)) { debug("For file '$file' $2 <= minexcludedversion= ".$minexcludedver{"$file"},3); next; }
				if (! $firstlineprinted) {
					print "$newlogcomment\n";
					$firstlineprinted=1;
				}
				$file=ExcludeRepositoryFromPath($file);
				print "\t* ".FormatDate($LogChangeDate{$logcomment}{$revision})." $LogChangeAuthor{$logcomment}{$revision}\t $file $version ($LogChangeState{$logcomment}{$revision})\n";
			}
			if ($firstlineprinted) { print "\n"; }
		}	
	}
	else {
		print "No change detected.\n";	
	}
}


# For building html report
if ($Output =~ /buildhtmlreport$/) {
    writeoutput("Generating HTML report...\n");


    my ($errorstringlines,$errorstringpie,$errorstringbars)=();
    if (!eval ('require "GD/Graph/lines.pm";')) { 
        $errorstringlines=($@?"Error: $@":"Error: Need Perl module GD::Graph::lines");
    }
    if (!eval ('require "GD/Graph/pie.pm";')) { 
        $errorstringpie=($@?"Error: $@":"Error: Need Perl module GD::Graph::pie");
    }
    if (!eval ('require "GD/Graph/bars.pm";')) { 
        $errorstringbars=($@?"Error: $@":"Error: Need Perl module GD::Graph::bars");
    }

    my $color_commit="#9988EE";
    my $color_file="#AA88BB";
    my $color_lightgrey="#F0F0F0";
    my $color_grey="#888888";
    
    # Made some calculation on commits by author
    my %nbcommit=(); my %nbfile=();
    my $nbtotalcommit=0; my $nbtotalfile=0;
    foreach my $key (sort keys %AuthorChangeCommit) {
        foreach my $file (keys %{$AuthorChangeCommit{$key}}) {
           $nbcommit{$key}+=$AuthorChangeCommit{$key}{$file};
           $nbfile{$key}++;
           $nbtotalcommit+=$AuthorChangeCommit{$key}{$file};
           $nbtotalfile++;
        }
    }
    
    # Made some calculation on state
    my %TotalCommitByState=('added'=>0,'changed'=>0,'removed'=>0);
    foreach my $dateuser (reverse sort keys %DateAuthor) {
        my ($date,$user)=split(/\s+/,$dateuser);
    	foreach my $logcomment (sort keys %{$DateAuthorLog{$dateuser}}) {
    		foreach my $filerevision (sort keys %{$DateAuthorLogFileRevState{$dateuser}{$logcomment}}) {
                my ($file,$revision)=split(/\s+/,$filerevision);
    			my $state=$DateAuthorLogFileRevState{$dateuser}{$logcomment}{$filerevision};
    			$state =~ s/_forced//;
                $TotalCommitByState{$state}++;
            }
        }
    }

print <<EOF;

<a name="menu">&nbsp;</a>
<table border="0" cellpadding="2" cellspacing="0" width="100%">
<tr><td>
<table class="aws_data" border="0" cellpadding="1" cellspacing="0" width="100%">
<tr><td class="awsm">$headstring</td></tr>
</table>
</td></tr></table>
<br />

<a name="summary">&nbsp;</a><br />
<table class="aws_border" border="0" cellpadding="2" cellspacing="0">
<tr><td class="aws_title" width="70%">Summary</td><td class="aws_blank">&nbsp;</td></tr>
<tr><td colspan="2">
<table class="aws_data summary" border="2" bordercolor="#ECECEC" cellpadding="2" cellspacing="0" width="100%">
EOF
print "<tr><td class=\"aws\" width=\"200\">Project module name</td><td class=\"aws\" colspan=\"2\"><b>$Module</b></td></tr>";
print "<tr><td class=\"aws\">Range analysis</td><td class=\"aws\" colspan=\"2\"><b>$rangestring</b></td></tr>";
print "<tr><td class=\"aws\">Date analysis</td><td class=\"aws\" colspan=\"2\"><b>".FormatDate("$nowyear-$nowmonth-$nowday $nowhour:$nowmin")."</b></td></tr>";
print "<tr><td bgcolor=\"FFF0E0\" class=\"aws\">Number of developers</td><td width=\"100\"><b>".(scalar keys %AuthorChangeCommit)."</b></td><td width=\"500\">&nbsp;</td></tr>";
print "<tr><td bgcolor=\"$color_commit\" class=\"aws\">Number of commits</td><td><b>$nbtotalcommit</b></td><td class=\"aws\"><b>$TotalCommitByState{'added'}</b> to add new file, <b>$TotalCommitByState{'changed'}</b> to change existing file, <b>$TotalCommitByState{'removed'}</b> to remove file</td></tr>";
print <<EOF;
</table></td></tr></table><br />

<br />

<a name="linesofcode">&nbsp;</a><br />
<table class="aws_border" border="0" cellpadding="2" cellspacing="0" width="100%">
<tr><td class="aws_title" width="70%">Lines of code*</td><td class="aws_blank">(* on non binary files only)</td></tr>
<tr><td colspan="2">
<table class="aws_data month" border="2" bordercolor="#ECECEC" cellpadding="2" cellspacing="0" width="100%">

<tr><td align="center">
<center>
EOF

# LINES OF CODE
#--------------

print "<table>";
print "<tr><td colspan=\"3\" class=\"aws\">This chart represents the balance between number of lines added and removed in non binary files (source files).</td></tr>\n";
print "<tr><td>&nbsp;</td>";
# Build chart
if ($errorstringlines) {
    print "<td>Perl module GD::Graph must be installed to get charts</td>";   
}
else {
    my @absi=(); my @ordo=(); my $cumul=0;
    my %yearmonth=();
    my $mincursor='';
    my $maxcursor='';
    foreach my $dateuser (sort keys %DateAuthor) {  # By ascending date
        my ($date,$user)=split(/\s+/,$dateuser);
        if ($date =~ /^(\d\d\d\d)(\d\d)\d\d/) {
        	foreach my $logcomment (sort keys %{$DateAuthorLog{$dateuser}}) {
        		foreach my $revision (sort keys %{$DateAuthorLogFileRevState{$dateuser}{$logcomment}}) {
                    my ($add,$del)=split(/\s+/,$DateAuthorLogFileRevLine{$dateuser}{$logcomment}{$revision});
                    $yearmonth{"$1$2"}+=int($add);
                    $yearmonth{"$1$2"}+=int($del);
                }
            }
            if (! $mincursor) { $mincursor="$1$2"; }
            $maxcursor="$1$2";
        }
    }
    # Define absi and ordo and complete holes
    my $cursor=$mincursor;
    do {
        $cumul+=$yearmonth{$cursor};
        push @ordo, $cumul;
        push @absi, substr($cursor,0,4)."-".substr($cursor,4,2);
        $cursor=~/(\d\d\d\d)(\d\d)/;
        $cursor=sprintf("%04d%02d",(int($1)+(int($2)>=12?1:0)),(int($2)>=12?1:(int($2)+1)));
    }
    until ($cursor > $maxcursor);
    # Build graph
    my $pngfile="${PROG}_${Module}_codelines.png";
    my @data = ([@absi],[@ordo]);
    my $graph = GD::Graph::lines->new(640, 240);
    $graph->set( 
          #title             => 'Some simple graph',
          transparent       =>1,
          x_label           =>'Month', x_label_position =>0.5, x_label_skip =>6, x_all_ticks =>1, x_long_ticks =>0, x_ticks =>1,
          y_label           =>'Code lines', y_min_value =>0, y_label_skip =>1, y_long_ticks =>1, y_tick_number =>10, #y_number_format   => "%06d",
          boxclr            =>$color_lightgrey,
          fgclr             =>$color_grey,
          line_types        =>[1, 2, 3],
          dclrs             => [ qw(blue green pink blue) ]
          #borderclrs        => [ qw(blue green pink blue) ],
    ) or die $graph->error;
    my $gd = $graph->plot(\@data) or die $graph->error;
    open(IMG, ">$pngfile") or die $!;
    binmode IMG;
    print IMG $gd->png;
    close IMG;
    # End build graph
    print "<td><img src=\"$pngfile\" border=\"0\"></td>";
}
print "<td>&nbsp;</td></tr>\n";
print "</table>\n";

print <<EOF;
</center>
</td></tr></table></td></tr></table><br />

<br />

<a name="developpers">&nbsp;</a><br />
<table class="aws_border" border="0" cellpadding="2" cellspacing="0" width="100%">
<tr><td class="aws_title" width="70%">Developers activity</td><td class="aws_blank">(* on non binary files only)</td></tr>
<tr><td colspan="2">
<table class="aws_data authors" border="2" bordercolor="#ECECEC" cellpadding="2" cellspacing="0" width="100%">
<tr bgcolor="#FFF0E0"><th width="140">Developer</th><th bgcolor="$color_commit" width="140">Number of commits</th><th bgcolor="$color_file" width="140">Different files commited</th><th bgcolor="#C1B2E2" width="140">Lines*<br>(added, modified, removed)</th><th bgcolor="#CEC2E8" width="140">Lines by commit*<br>(added, modified, removed)</th><th bgcolor="#88A495" width="140">Last commit</th><th>&nbsp; </th></tr>
EOF

# BY DEVELOPERS
#--------------

foreach my $key (reverse sort { $nbcommit{$a} <=> $nbcommit{$b} } keys %nbcommit) {
    print "<tr><td class=\"aws\">";
    print $key;
    print "</td><td>";
    print $nbcommit{$key};
    print "</td><td>";
    print $nbfile{$key};
    print "</td><td>";
    print $AuthorChangeLineAdd{$key}." / ".$AuthorChangeLineChange{$key}." / ".$AuthorChangeLineDel{$key};
    print "</td><td>";
    print RoundNumber($AuthorChangeLineAdd{$key}/$nbcommit{$key},1)." / ".RoundNumber($AuthorChangeLineChange{$key}/$nbcommit{$key},1)." / ".RoundNumber($AuthorChangeLineDel{$key}/$nbcommit{$key},1);
    print "</td><td>";
    print FormatDate($AuthorChangeLast{$key},'simple');
    print "</td>";
    print "<td>&nbsp;</td>";
    print "</tr>";
}
if (scalar keys %nbcommit > 1) {
    if ($errorstringpie) {
        print "<tr><td colspan\"7\">Perl module GD::Graph::pie must be installed to get charts</td></tr>";
    }
    else {
        my $MAXABS=12;
        # TODO lmité à 5
        my $col;
        # Build graph
        my $pngfilenbcommit="${PROG}_${Module}_developerscommit.png";
        my @data = ([keys %nbcommit],[values %nbcommit]);
        my $graph = GD::Graph::pie->new(160, 138);
        $col=$color_commit; $col=~s/#//;
        $graph->set( 
              title             => 'Number of commits',
              axislabelclr      => qw(black),
              textclr           => $color_commit,
              transparent       => 1,
              accentclr         => $color_grey,
              dclrs             => [ map{ sprintf("#%06x",(hex($col)+(hex("050501")*$_))) } (1..$MAXABS) ]
        ) or die $graph->error;
        my $gd = $graph->plot(\@data) or die $graph->error;
        open(IMG, ">$pngfilenbcommit") or die $!;
        binmode IMG;
        print IMG $gd->png;
        close IMG;
        # End build graph
        # Build graph
        my $pngfilefile="${PROG}_${Module}_developersfile.png";
        my @data = ([keys %nbfile],[values %nbfile]);
        my $graph = GD::Graph::pie->new(160, 138);
        $col=$color_file; $col=~s/#//;
        $graph->set( 
              title             => 'Different files',
              axislabelclr      => qw(black),
              textclr           => $color_file,
              transparent       => 1,
              accentclr         => $color_grey,
              dclrs             => [ map{ sprintf("#%06x",(hex($col)+(hex("050503")*$_))) } (1..$MAXABS) ]
        ) or die $graph->error;
        my $gd = $graph->plot(\@data) or die $graph->error;
        open(IMG, ">$pngfilefile") or die $!;
        binmode IMG;
        print IMG $gd->png;
        close IMG;
        # End build graph
        print "<tr><td colspan=\"7\"><img src=\"$pngfilenbcommit\" border=\"0\"> &nbsp;  &nbsp;  &nbsp;  &nbsp;  &nbsp;  &nbsp;  &nbsp;  &nbsp;  &nbsp;  &nbsp; <img src=\"$pngfilefile\" border=\"0\"></td></tr>\n";
    }
}
print <<EOF;
</table></td></tr></table><br />

<br />

<a name="daysofweek">&nbsp;</a><br />
<table class="aws_border" border="0" cellpadding="2" cellspacing="0" width="100%">
<tr><td class="aws_title" width="70%">Activity by days of week</td><td class="aws_blank"></td></tr>
<tr><td colspan="2">
<table class="aws_data daysofweek" border="2" bordercolor="#ECECEC" cellpadding="2" cellspacing="0" width="100%">
EOF

# BY DAYS OF WEEK
#----------------

if ($errorstringbars) {
    print "<tr><td>Perl module GD::Graph::bars must be installed to get charts</td></tr>";
}
else {
    my @absi=('Mon','Tue','Wed','Thi','Fri','Sat','Sun'); my @ordo=(); my $cumul=0;
    # We need to build array values for chart
    foreach my $dateuser (sort keys %DateAuthor) {
        my ($date,$user)=split(/\s+/,$dateuser);
        my $dayofweek=&DayOfWeek($date);
        $ordo[$dayofweek-1]+=$DateAuthor{"$dateuser"};
    }
    # Build graph
    my $pngfile="${PROG}_${Module}_daysofweek.png";
    my @data = ([@absi],[@ordo]);
    my $graph = GD::Graph::bars->new(260, 200);
    $graph->set( 
          #title             => 'Some simple graph',
          transparent       => 1,
          x_label           => 'Days of week', x_label_position =>0.5, x_all_ticks =>1, x_long_ticks =>0, x_ticks =>1, x_number_format => "%02d",
          y_label           => 'Number of commits', y_min_value =>0, y_label_skip =>1, y_long_ticks =>1, y_tick_number =>10, #y_number_format   => "%06d",
          textclr           => $color_commit,
          boxclr            => $color_lightgrey,
          fgclr             => $color_grey,
          dclrs             => [ $color_commit ],
          accentclr         => "#444444",
          #borderclrs        => [ qw(blue green pink blue) ],
    ) or die $graph->error;
    my $gd = $graph->plot(\@data) or die $graph->error;
    open(IMG, ">$pngfile") or die $!;
    binmode IMG;
    print IMG $gd->png;
    close IMG;
    # End build graph
    print "<tr><td align=\"center\"><img src=\"$pngfile\" border=\"0\"></td></tr>";
}

print <<EOF;
</table></td></tr></table><br />

<br />
<a name="hours">&nbsp;</a><br />
<table class="aws_border" border="0" cellpadding="2" cellspacing="0" width="100%">
<tr><td class="aws_title" width="70%">Activity by hours</td><td class="aws_blank"></td></tr>
<tr><td colspan="2">
<table class="aws_data hours" border="2" bordercolor="#ECECEC" cellpadding="2" cellspacing="0" width="100%">
EOF

# BY HOURS
#---------

if ($errorstringbars) {
    print "<tr><td>Perl module GD::Graph::bars must be installed to get charts</td></tr>";
}
else {
    my @absi=(0..23); my @ordo=(); my $cumul=0;
    # We need to build array values for chart
    foreach my $houruser (sort keys %HourAuthor) {
        my ($hour,$user)=split(/\s+/,$houruser);
        $ordo[int($hour)]+=$HourAuthor{"$houruser"};
    }
    # Build graph
    my $pngfile="${PROG}_${Module}_hours.png";
    my @data = ([@absi],[@ordo]);
    my $graph = GD::Graph::bars->new(640, 240);
    $graph->set( 
          #title             => 'Some simple graph',
          transparent       => 1,
          x_label           => 'Hours', x_label_position =>0.5, x_all_ticks =>1, x_long_ticks =>0, x_ticks =>1, x_number_format => "%02d",
          y_label           => 'Number of commits', y_min_value =>0, y_label_skip =>1, y_long_ticks =>1, y_tick_number =>10, #y_number_format   => "%06d",
          textclr           => $color_commit,
          boxclr            => $color_lightgrey,
          fgclr             => $color_grey,
          dclrs             => [ $color_commit ],
          accentclr         => "#444444",
          #borderclrs        => [ qw(blue green pink blue) ],
    ) or die $graph->error;
    my $gd = $graph->plot(\@data) or die $graph->error;
    open(IMG, ">$pngfile") or die $!;
    binmode IMG;
    print IMG $gd->png;
    close IMG;
    # End build graph
    print "<tr><td align=\"center\"><img src=\"$pngfile\" border=\"0\"></td></tr>";
}

print <<EOF;
</table></td></tr></table><br />

<br />

<a name="lastlogs">&nbsp;</a><br />
<table class="aws_border" border="0" cellpadding="2" cellspacing="0" width="100%">
<tr><td class="aws_title" width="70%">Last commit logs</td><td class="aws_blank">&nbsp;</td></tr>
<tr><td colspan="2">
<table class="aws_data lastlogs" border="2" bordercolor="#ECECEC" cellpadding="2" cellspacing="0" width="100%">
EOF

# LASTLOGS
#---------

my $width=140;
print "<tr bgcolor=\"#FFF0E0\"><th width=\"$width\">Date</th><th width=\"$width\">Developers</th><th class=\"aws\">Last ".($MAXLASTLOG?"$MAXLASTLOG ":"")."Commit Logs</th></tr>";
my $cursor=0;
foreach my $dateuser (reverse sort keys %DateAuthor) {
    my ($date,$user)=split(/\s+/,$dateuser);
    print "<tr><td valign=\"top\">".FormatDate($date)."</td>";
    print "<td valign=\"top\">".$user."</td>";
    print "<td class=\"aws\">";
	foreach my $logcomment (sort keys %{$DateAuthorLog{$dateuser}}) {
        $cursor++;
        my $comment=$logcomment;
		chomp $comment;
		$comment =~ s/\r$//;
		foreach my $logline (split(/\n/,$comment)) {
			print "<b>".CleanFromTags($logline)."</b><br>\n";
		}
		foreach my $revision (reverse sort keys %{$DateAuthorLogFileRevState{$dateuser}{$logcomment}}) {
			$revision=~/(.*)\s([\d\.]+)/;
			my ($file,$version)=($1,$2);
			if ($maxincludedver{"$file"} && (CompareVersionBis($2,$maxincludedver{"$file"}) > 0)) { debug("For file '$file' $2 > maxincludedversion= ".$maxincludedver{"$file"},3); next; }
			if ($minexcludedver{"$file"} && (CompareVersionBis($2,$minexcludedver{"$file"}) <= 0)) { debug("For file '$file' $2 <= minexcludedversion= ".$minexcludedver{"$file"},3); next; }
			my $state=$DateAuthorLogFileRevState{$dateuser}{$logcomment}{$revision};
			$state =~ s/_forced//;
			my %colorstate=('added'=>'#008822','changed'=>'#888888','removed'=>'#880000');
			print "* ".FormatDiffLink(ExcludeRepositoryFromPath($file),$version)." $version (".FormatState($state);
			print ($state eq 'added'?" <font color=\"#008822\">".$DateAuthorLogFileRevLine{$dateuser}{$logcomment}{$revision}."</font>":"");
			print ($state eq 'changed'?" <font color=\"#888888\">".$DateAuthorLogFileRevLine{$dateuser}{$logcomment}{$revision}."</font>":"");
			print ($state eq 'removed'?" <font color=\"#880000\">".$DateAuthorLogFileRevLine{$dateuser}{$logcomment}{$revision}."</font>":"");
			print ")<br>\n";
		}
        if ($MAXLASTLOG && $cursor >= $MAXLASTLOG) { last; }
	}
    print "</td></tr>";
    if ($MAXLASTLOG && $cursor >= $MAXLASTLOG) {
        my $rest="some"; # TODO put here value of not shown commits
        print "<tr><td valign=\"top\" colspan=\"3\" align=\"left\">Other commits are hidden...</td></tr>";
        last;
    }
}	

print <<EOF;
</table></td></tr></table><br />
EOF

}   # End buildhtmlreport

# Footer
if ($Output =~ /buildhtmlreport$/) {
    print "<br />\n";
	print "<b><a href=\"http://cvschangelogb.sourceforge.net\" target=\"awstatshome\">Created by $PROG $VERSION</a></b>";
    print "<br />\n";
	print "<br />\n";
	print "</body>\n</html>\n";
}


print STDERR ucfirst($PROG)." finished successfully.\n";


0;
