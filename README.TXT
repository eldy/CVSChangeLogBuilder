
------------- AWBot --------------
         cvschangelogbuilder
----------------------------------

cvschangelogbuilder is an utility to generate a changelog for a project
hosted on a CVS server. The main goal is to provide a better output
that the 'cvs log' command and to permit to choose the sorting criteria.
Another feature is that cvschangelogbuilder is able to show all the changes
between two versions, even if versions are not in main branch. It also
add information to know if file was added, changed or removed for
delta output (only possible if inital and final version are in main
branch).
cvschangelogbuilder offer 4 kinds of output:
listdeltaforrpm	    To build a changelog to include in a rpm .spec file.
listdeltabydate	    To build a changelog by date (looks near 'cvs log').
listdeltabyfile	    To build a changelog by file.
listdeltabylog      To build a changelog by change comment.
buildhtmlreport     To build an html report of project CVS activity.

License: GNU GPL (GNU General Public License. See COPYING.TXT file)
Version : 2.5
Release date: August 2010
Platforms: All (Linux, NT, BSD, Solaris and other *NIX's, BeOS, OS/2...)
Author: Laurent Destailleur <eldy@users.sourceforge.net>
cvschangelogbuilder official web site and latest version: http://cvschangelogb.sourceforge.net


I - Files
---------
	The distribution of cvschangelogbuilder package includes the following files:
	README.TXT                      This file
	cvschangelogbuilder.pl          The cvschangelogbuilder tool.
	docs/*                          The changelog and PAD files.
    

II - ABOUT THE AUTHOR, LICENSE AND SUPPORT
-------------------------------------------
Copyright (C) 2003-2010 - Laurent Destailleur - eldy@users.sourceforge.net

This program is free software; you can redistribute it and/or
modify it under the terms of the GNU General Public License
version 2 as published by the Free Software Foundation.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details, in COPYING.TXT file.

If you have not received a copy of this file along with this program, write to
the Free Software Foundation, Inc.,
59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
